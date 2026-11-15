/*************************************************************************
 * Incremental Parametric Cut (IPC) procedure for the densest subgraph problem -- Version 2
 *
 * Same input, options, algorithm and output as Version 1.0 (src/1.0/IPC-DSP.c): reads "n m", the
 * optional node weights and values, and then m lines "TAIL HEAD [WEIGHT]" (nodes labeled 1..n)
 * from stdin.
 *
 * Changes with respect to Version 1.0:
 *   - arcs are 24 bytes: endpoints, 64-bit flow and capacity (exact integers scaled by APP_VAL),
 *     with the direction flag in the top bit of `to`. The intercept and slope of the source-adjacent
 *     and sink-adjacent arcs are derived from the node (intercept = degree * APP_VAL, slope = weight);
 *   - nodes are 48 bytes and use 4-byte indices instead of pointers;
 *   - root buckets are FIFO queues of node indices;
 *   - out-of-tree entries are 4-byte arc indices;
 *   - lists of the arcs with both ends in S and of the nodes of S are compacted after every cut;
 *     S only shrinks, so C(S,S), q(S) and the capacity update touch only what is still in S;
 *   - the capacity update between iterations is done in two passes over the nodes of S (see
 *     updateCapacities), instead of one walk to the root of the tree per node;
 *   - each edge is credited to its endpoint of larger label (Version 1.0: smaller label). The densest
 *     subgraph and the sequence of lambda values are the same.
 *
 * Copyright (c) 2024. The Regents of the University of California (Regents). All Rights Reserved.
 * See LICENSE.md.
 *************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int uint;
typedef long long ll;
#define NONE 0xffffffffu
#define INBUCKET_END 0xfffffffeu   /* `next` of the last node in a bucket: non-NONE means "in a bucket" */
#define DIRBIT 0x80000000u

typedef struct { uint from, toDir; ll flow, capacity; } Arc;   /* 24 bytes */
typedef struct
{
    ll excess;
    uint parent, childList, nextScan, arcToParent, next, prev, numOutOfTree, nextArc, oot;
} Node;                                                         /* 48 bytes */
typedef uint Oot;
typedef struct { uint start, end; } Root;

static ll APP_VAL = 10000LL;
static int DECIMALS = 4;
static int n, m, numNodes, numArcs, weightedEdges, weightedNodes, valuedNodes, hasInjectedLambda;
static uint source = 0, sink = 1;
static double injectedLambda = 0.0, TOL = 1e-5;
static ll currLambda = 0;
static uint highestStrongLabel = 1, maxStrongBucket = 0;
static Node *nodes; static Arc *arcs; static Oot *oot; static Root *strongRoots;
static int *labels, *labelCount, *weights, *degrees, *values;
static char *bestSourceSet;
static ll bestCSS, bestQS;
static uint *liveArc, numLiveArc, *liveVert, numLiveVert;   /* internal arcs inside S, vertices in S */
static FILE *dumpSourceSetFile;

static inline uint arcTo(const Arc *a) { return a->toDir & ~DIRBIT; }
static inline uint arcDir(const Arc *a) { return a->toDir >> 31; }
static inline void setDir(Arc *a, uint d) { a->toDir = (a->toDir & ~DIRBIT) | (d ? DIRBIT : 0); }
static inline ll lmax(ll a, ll b) { return a > b ? a : b; }
/* b > 0; C division truncates toward zero, so adjust for negative a */
static inline ll ceil_div(ll a, ll b) { return (a >= 0) ? (a + b - 1) / b : -((-a) / b); }
static inline ll floor_div(ll a, ll b) { return (a >= 0) ? a / b : -((-a + b - 1) / b); }
static double fmax_(double a, double b) { return a > b ? a : b; }

/* terminal arcs: index m + 2i is the source arc of vertex i (node i+2), m + 2i + 1 its sink arc */
static inline ll intercept(uint a) { return (ll)degrees[(a - m) >> 1] * APP_VAL; }
static inline ll slope(uint a) { return (ll)weights[(a - m) >> 1]; }
static ll computeArcCapacity(uint a, ll param)
{
    if ((int)a < m) return arcs[a].capacity;                     /* internal: constant */
    if (arcTo(&arcs[a]) == sink) return lmax(intercept(a) - param * slope(a), 0);
    return lmax(param * slope(a) - intercept(a), 0);
}

static inline void addOutOfTreeNode(uint v, uint a)
{
    Oot *e = &oot[nodes[v].oot + nodes[v].numOutOfTree++];
    *e = a;
}
static inline void addToStrongBucket(uint v, uint label)
{
    if (label > maxStrongBucket) maxStrongBucket = label;
    Root *b = &strongRoots[label];
    if (b->start != NONE) { nodes[b->end].next = v; b->end = v; } else { b->start = b->end = v; }
    nodes[v].next = INBUCKET_END;
}
static inline uint popBucket(uint label)   /* remove the first node; returns it */
{
    Root *b = &strongRoots[label]; uint r = b->start;
    b->start = (nodes[r].next == INBUCKET_END) ? NONE : nodes[r].next;
    if (b->start == NONE) b->end = NONE;
    return r;
}
static inline void addRelationship(uint np, uint c)
{
    nodes[c].parent = np; nodes[c].next = nodes[np].childList;
    if (nodes[np].childList != NONE) nodes[nodes[np].childList].prev = c;
    nodes[np].childList = c;
}
static inline void breakRelationship(uint op, uint c)
{
    nodes[c].parent = NONE;
    if (nodes[op].childList == c) { nodes[op].childList = nodes[c].next; nodes[c].next = NONE; return; }
    uint cur = nodes[c].prev;
    nodes[cur].next = nodes[c].next;
    if (nodes[c].next != NONE) nodes[nodes[c].next].prev = cur;
    nodes[c].next = NONE;
}
static void liftAll(uint root)
{
    uint temp, cur = root;
    nodes[cur].nextScan = nodes[cur].childList;
    --labelCount[labels[cur]]; labels[cur] = numNodes;
    for (; cur != NONE; cur = nodes[cur].parent)
        while (nodes[cur].nextScan != NONE)
        {
            temp = nodes[cur].nextScan; nodes[cur].nextScan = nodes[temp].next; cur = temp;
            nodes[cur].nextScan = nodes[cur].childList;
            --labelCount[labels[cur]]; labels[cur] = numNodes;
        }
}
static void merge(uint parent, uint child, uint newArc)
{
    uint oldArc, cur = child, oldParent, newParent = parent;
    while (nodes[cur].parent != NONE)
    {
        oldArc = nodes[cur].arcToParent; nodes[cur].arcToParent = newArc;
        oldParent = nodes[cur].parent;
        breakRelationship(oldParent, cur); addRelationship(newParent, cur);
        newParent = cur; cur = oldParent; newArc = oldArc;
        setDir(&arcs[newArc], 1 - arcDir(&arcs[newArc]));
    }
    nodes[cur].arcToParent = newArc; addRelationship(newParent, cur);
}
static inline void pushUpward(uint a, uint child, uint parent, ll resCap)
{
    if (resCap >= nodes[child].excess)
    { nodes[parent].excess += nodes[child].excess; arcs[a].flow += nodes[child].excess; nodes[child].excess = 0; return; }
    setDir(&arcs[a], 0);
    nodes[parent].excess += resCap; nodes[child].excess -= resCap;
    arcs[a].flow = arcs[a].capacity;
    addOutOfTreeNode(parent, a); breakRelationship(parent, child);
    addToStrongBucket(child, labels[child]);
}
static inline void pushDownward(uint a, uint child, uint parent, ll flow)
{
    if (flow >= nodes[child].excess)
    { nodes[parent].excess += nodes[child].excess; arcs[a].flow -= nodes[child].excess; nodes[child].excess = 0; return; }
    setDir(&arcs[a], 1);
    nodes[child].excess -= flow; nodes[parent].excess += flow;
    arcs[a].flow = 0;
    addOutOfTreeNode(parent, a); breakRelationship(parent, child);
    addToStrongBucket(child, labels[child]);
}
static void pushExcess(uint root)
{
    uint cur, parent;
    for (cur = root; nodes[cur].excess && nodes[cur].parent != NONE; cur = parent)
    {
        parent = nodes[cur].parent; uint a = nodes[cur].arcToParent;
        if (arcDir(&arcs[a])) pushUpward(a, cur, parent, arcs[a].capacity - arcs[a].flow);
        else pushDownward(a, cur, parent, arcs[a].flow);
    }
    if (nodes[cur].excess > 0 && nodes[cur].next == NONE) addToStrongBucket(cur, labels[cur]);
}
static uint findWeakNode(uint sn, uint *weak)
{
    uint i, size = nodes[sn].numOutOfTree; int want = (int)highestStrongLabel - 1;
    Oot *L = &oot[nodes[sn].oot];
    for (i = nodes[sn].nextArc; i < size; ++i)
    {
        uint a = L[i], to = arcTo(&arcs[a]), from = arcs[a].from;
        if (labels[to] == want)
        { nodes[sn].nextArc = i; *weak = to; --nodes[sn].numOutOfTree; L[i] = L[nodes[sn].numOutOfTree]; return a; }
        else if (labels[from] == want)
        { nodes[sn].nextArc = i; *weak = from; --nodes[sn].numOutOfTree; L[i] = L[nodes[sn].numOutOfTree]; return a; }
    }
    nodes[sn].nextArc = nodes[sn].numOutOfTree;
    return NONE;
}
static void checkChildren(uint cur)
{
    const int lab = labels[cur];
    for (; nodes[cur].nextScan != NONE; nodes[cur].nextScan = nodes[nodes[cur].nextScan].next)
        if (labels[nodes[cur].nextScan] == lab) return;
    --labelCount[lab]; labels[cur] = lab + 1; ++labelCount[lab + 1];
    nodes[cur].nextArc = 0;
}
static void processRoot(uint root)
{
    uint temp, sn = root, weak, out;
    nodes[root].nextScan = nodes[root].childList;
    if ((out = findWeakNode(root, &weak)) != NONE) { merge(weak, sn, out); pushExcess(root); return; }
    checkChildren(root);
    while (sn != NONE)
    {
        while (nodes[sn].nextScan != NONE)
        {
            temp = nodes[sn].nextScan; nodes[sn].nextScan = nodes[temp].next; sn = temp;
            nodes[sn].nextScan = nodes[sn].childList;
            if ((out = findWeakNode(sn, &weak)) != NONE) { merge(weak, sn, out); pushExcess(root); return; }
            checkChildren(sn);
        }
        sn = nodes[sn].parent;
        if (sn != NONE) checkChildren(sn);
    }
    addToStrongBucket(root, labels[root]);
    ++highestStrongLabel;
}
static uint getHighestStrongRoot(void)
{
    uint i, r;
    for (i = highestStrongLabel; i > 0; --i)
        if (strongRoots[i].start != NONE)
        {
            highestStrongLabel = i;
            if (labelCount[i - 1]) { r = popBucket(i); nodes[r].next = NONE; return r; }
            while (strongRoots[i].start != NONE) { r = popBucket(i); liftAll(r); }
        }
    if (strongRoots[0].start == NONE) return NONE;
    while (strongRoots[0].start != NONE)
    {
        r = popBucket(0);
        labels[r] = 1; --labelCount[0]; ++labelCount[1];
        addToStrongBucket(r, 1);
    }
    highestStrongLabel = 1;
    r = popBucket(1); nodes[r].next = NONE;
    return r;
}
static void solve(void) { uint r; while ((r = getHighestStrongRoot()) != NONE) processRoot(r); }

/* Capacity update between iterations. Lazy two-pass update, O(live vertices) for any tree depth, same flows as
 * one walk to the root per vertex:
 *   pass 1: apply the source-arc and sink-arc changes of every live vertex; from each vertex that has excess, walk up
 *           marking unmarked ancestors (stop at the first marked vertex or at the root); walks stored top-down;
 *   pass 2: read the list backwards (children before parents) and push each vertex's accumulated excess over one
 *           arc; roots left with excess enter the strong buckets. Extra memory: 8 bytes per vertex. */
static uint *mkList, *mkStamp, mkEpoch = 0;
static void updateCapacities(void)
{
    ll param = currLambda;
    maxStrongBucket = 0;
    ++mkEpoch;
    uint len = 0;
    for (uint k = 0; k < numLiveVert; ++k)
    {
        uint vi = liveVert[k], a = m + 2 * vi, v = vi + 2;
        if (labels[v] >= numNodes) continue;
        ll delta = computeArcCapacity(a, param) - arcs[a].capacity;
        if (delta < 0) { printf("c Error on source-adjacent arc: capacity decreases\n"); exit(0); }
        arcs[a].capacity += delta; arcs[a].flow += delta; nodes[v].excess += delta;
        a = m + 2 * vi + 1;
        delta = computeArcCapacity(a, param) - arcs[a].capacity;
        if (delta > 0) { printf("c Error on sink-adjacent arc: capacity increases\n"); exit(0); }
        arcs[a].capacity += delta; arcs[a].flow += delta; nodes[v].excess -= delta;
        if (nodes[v].excess <= 0) continue;             /* nothing to push */
        uint st = len;
        for (uint cur = v; cur != NONE && mkStamp[cur] != mkEpoch; cur = nodes[cur].parent) { mkStamp[cur] = mkEpoch; mkList[len++] = cur; }
        for (uint x = st, y = len; x + 1 < y; ++x) { --y; uint t = mkList[x]; mkList[x] = mkList[y]; mkList[y] = t; }
    }
    for (uint h = len; h-- > 0; )
    {
        uint cur = mkList[h];
        if (nodes[cur].excess <= 0) continue;
        if (nodes[cur].parent == NONE) { if (nodes[cur].next == NONE) addToStrongBucket(cur, labels[cur]); continue; }
        uint parent = nodes[cur].parent, a = nodes[cur].arcToParent;
        if (arcDir(&arcs[a])) pushUpward(a, cur, parent, arcs[a].capacity - arcs[a].flow);
        else pushDownward(a, cur, parent, arcs[a].flow);
    }
    highestStrongLabel = maxStrongBucket;
}

/* S = vertices not lifted to label numNodes; C(S,S) (plus the node values of S) and q(S) by one pass */
static void measureS(ll *css, ll *qs)
{
    ll c = 0, q = 0; uint w = 0;
    for (uint k = 0; k < numLiveArc; k++)       /* compact: an arc that leaves S never comes back */
    {
        uint i = liveArc[k];
        if (labels[arcs[i].from] < numNodes && labels[arcTo(&arcs[i])] < numNodes) { c += arcs[i].capacity; liveArc[w++] = i; }
    }
    numLiveArc = w; w = 0;
    for (uint k = 0; k < numLiveVert; k++)
    {
        uint i = liveVert[k];
        if (labels[i + 2] < numNodes) { q += weights[i]; c += (ll)values[i] * APP_VAL; liveVert[w++] = i; }
    }
    numLiveVert = w;
    *css = c; *qs = q;
}
static void copySourceSet(ll css, ll qs)
{
    for (int i = 0; i < n; i++) bestSourceSet[i] = (labels[i + 2] < numNodes);
    bestCSS = css; bestQS = qs;
}

/* ---- input (stdin) ---- */
static char ibuf[1 << 22]; static size_t ilen = 0, ipos = 0;
static int nextChar(void)
{
    if (ipos == ilen) { ilen = fread(ibuf, 1, sizeof ibuf, stdin); ipos = 0; if (ilen == 0) return -1; }
    return ibuf[ipos++];
}
static int readInt(void)   /* skips to the next integer; a '-' right before the digits makes it negative */
{
    int c = nextChar(), r = 0, sign = 1;
    while (c != -1 && (c < '0' || c > '9')) { sign = (c == '-') ? -1 : 1; c = nextChar(); }
    while (c >= '0' && c <= '9') { r = r * 10 + (c - '0'); c = nextChar(); }
    return sign * r;
}

static void printHelp(const char *prog)
{
    printf("Usage : %s [OPTIONS]                                        \n\n", prog);
    printf("Options:\n");
    printf("  --help                 print this help message                \n");
    printf("  --accuracy N           set the accuracy to N decimal places   \n");
    printf("                         note that a big N may induce errors on \n");
    printf("                         graphs that are big or have big weights\n");
    printf("                         by default, 4 decimal places           \n");
    printf("  --startLambda L        start incremental procedure with L     \n");
    printf("  --weightedEdges        enable if input has weights on edges   \n");
    printf("  --weightedNodes        enable if input has weights on nodes   \n");
    printf("  --valuedNodes          enable if input has values on nodes    \n");
    printf("                         (integers of any sign, added to the    \n");
    printf("                         numerator, like a self-loop)           \n");
    printf("  --dumpDensest FILE     dump list of nodes in optimal solution \n");
    printf("                         to FILE                                \n");
    printf("\n\nNote that this program read from stdin\n");
    printf("An example command is '%s < mygraph.txt' to read from file\n", prog);
    printf("\n");
    printf("The input is an undirected graph with N nodes (labeled 1..N)\n");
    printf("and M edges. All fields are integers. Optional fields, shown\n");
    printf("in [ ], appear only if their option is given:\n");
    printf("  WEIGHT_NODE_i  node weight (denominator), --weightedNodes, default 1\n");
    printf("  VALUE_NODE_i   node value (numerator),    --valuedNodes,   default 0\n");
    printf("  WEIGHT_EDGE_k  edge weight (numerator),   --weightedEdges, default 1\n");
    printf("Each edge is listed once, as TAIL HEAD with TAIL < HEAD.\n");
    printf("\n");
    printf("The format of the input is as follows: \n");
    printf("\n");
    printf("N M\n");
    printf("[WEIGHT_NODE_1] [VALUE_NODE_1]\n");
    printf("...\n");
    printf("[WEIGHT_NODE_N] [VALUE_NODE_N]\n");
    printf("TAIL_EDGE_1 HEAD_EDGE_1 [WEIGHT_EDGE_1]\n");
    printf("...\n");
    printf("TAIL_EDGE_M HEAD_EDGE_M [WEIGHT_EDGE_M]\n");
}

int main(int argc, char **argv)
{
    for (int i = 1; i < argc; i++)
    {
        if (!strcmp(argv[i], "--accuracy")) { int acc = atoi(argv[++i]); DECIMALS = acc; APP_VAL = 1; for (int z = 0; z < acc; z++) APP_VAL *= 10LL; }
        else if (!strcmp(argv[i], "--help")) { printHelp(argv[0]); exit(0); }
        else if (!strcmp(argv[i], "--startLambda")) { injectedLambda = atof(argv[++i]); hasInjectedLambda = 1; }
        else if (!strcmp(argv[i], "--weightedEdges")) weightedEdges = 1;
        else if (!strcmp(argv[i], "--weightedNodes")) weightedNodes = 1;
        else if (!strcmp(argv[i], "--valuedNodes")) valuedNodes = 1;
        else if (!strcmp(argv[i], "--dumpDensest")) dumpSourceSetFile = fopen(argv[++i], "w");
        else { printf("%s: invalid argument %s\n", argv[0], argv[i]); printf("Try '%s --help' for more information.\n", argv[0]); exit(-1); }
    }
    printf("c Incremental cut procedure for maximum subgraph density\n");
    n = readInt(); m = readInt();
    printf("c n=%d m=%d\n", n, m);
    numNodes = n + 2; numArcs = m + 2 * n;
    weights = (int *)malloc(n * sizeof(int)); degrees = (int *)calloc(n, sizeof(int)); values = (int *)calloc(n, sizeof(int));
    bestSourceSet = (char *)malloc(n); labels = (int *)calloc(numNodes, sizeof(int));
    labelCount = (int *)calloc(numNodes + 1, sizeof(int));
    strongRoots = (Root *)malloc((numNodes + 1) * sizeof(Root));
    nodes = (Node *)malloc(numNodes * sizeof(Node)); arcs = (Arc *)malloc((size_t)numArcs * sizeof(Arc));
    if (!weights || !degrees || !values || !bestSourceSet || !labels || !labelCount || !strongRoots || !nodes || !arcs) { printf("Could not allocate memory.\n"); exit(1); }
    for (int i = 0; i < n; i++) { weights[i] = weightedNodes ? readInt() : 1; if (valuedNodes) values[i] = readInt(); }
    for (int i = 0; i <= numNodes; i++) strongRoots[i].start = strongRoots[i].end = NONE;
    for (int i = 0; i < numNodes; i++)
    { Node *x = &nodes[i]; x->excess = 0; x->parent = x->childList = x->nextScan = x->arcToParent = x->next = x->prev = NONE;
      x->numOutOfTree = 0; x->nextArc = 0; x->oot = 0; }
    uint *incid = (uint *)calloc(numNodes, sizeof(uint));
    if (!incid) { printf("Could not allocate memory.\n"); exit(1); }
    for (int i = 0; i < m; i++)
    {
        int u = readInt(), v = readInt(), w = weightedEdges ? readInt() : 1;
        { int t = u; u = v; v = t; }             /* credit the edge to its endpoint of larger label */
        degrees[u - 1] += w;
        Arc *a = &arcs[i];                       /* arc v -> u */
        a->from = (uint)(v + 1); a->toDir = (uint)(u + 1) | DIRBIT; a->flow = 0; a->capacity = (ll)w * APP_VAL;
        ++incid[a->from]; ++incid[u + 1];          /* incidence count, turned into offsets below */
    }
    for (int i = 0; i < n; i++)
    {
        Arc *sa = &arcs[m + 2 * i], *ta = &arcs[m + 2 * i + 1];
        sa->from = source; sa->toDir = (uint)(i + 2) | DIRBIT; sa->flow = 0; sa->capacity = 0;
        ta->from = (uint)(i + 2); ta->toDir = sink | DIRBIT; ta->flow = 0; ta->capacity = 0;
        ++incid[source]; incid[i + 2] += 2; ++incid[sink];
    }
    /* a node value acts as a self-loop of that weight: it is added to the degree of the node */
    for (int i = 0; i < n; i++) degrees[i] += values[i];
    /* initial lambda = density of the whole graph */
    { ll num = 0, den = 0; for (int i = 0; i < m; i++) num += arcs[i].capacity;
      for (int i = 0; i < n; i++) { num += (ll)values[i] * APP_VAL; den += weights[i]; }
      currLambda = floor_div(num, den); }
    if (hasInjectedLambda) currLambda = lmax(currLambda, (ll)(injectedLambda * APP_VAL));
    printf("c Initial lambda = %.*lf\n", DECIMALS, (double)currLambda / APP_VAL);
    for (int i = m; i < numArcs; i++) arcs[i].capacity = computeArcCapacity(i, currLambda);
    { size_t off = 0; for (int i = 0; i < numNodes; i++) { nodes[i].oot = (uint)off; off += incid[i]; }
      free(incid);
      oot = (Oot *)malloc((off ? off : 1) * sizeof(Oot)); if (!oot) { printf("Could not allocate memory.\n"); exit(1); } }
    for (int i = 0; i < numArcs; i++)
    {
        uint from = arcs[i].from, to = arcTo(&arcs[i]);
        if (to == source || from == sink || from == to) continue;
        if (from == source) addOutOfTreeNode(from, i);
        else if (to == sink) addOutOfTreeNode(to, i);
        else addOutOfTreeNode(from, i);
    }
    /* simple initialization */
    for (uint i = 0; i < nodes[source].numOutOfTree; i++)
    {
        uint a = oot[nodes[source].oot + i];
        arcs[a].flow = arcs[a].capacity; nodes[arcTo(&arcs[a])].excess += arcs[a].capacity;
    }
    for (uint i = 0; i < nodes[sink].numOutOfTree; i++)
    {
        uint a = oot[nodes[sink].oot + i];
        arcs[a].flow = arcs[a].capacity; nodes[arcs[a].from].excess -= arcs[a].capacity;
    }
    nodes[source].excess = 0; nodes[sink].excess = 0;
    for (int i = 0; i < numNodes; i++)
        if (nodes[i].excess > 0) { labels[i] = 1; ++labelCount[1]; addToStrongBucket(i, 1); }
    labels[source] = numNodes; labels[sink] = 0;
    labelCount[0] = (numNodes - 2) - labelCount[1];

    liveArc = (uint *)malloc((m ? m : 1) * sizeof(uint)); liveVert = (uint *)malloc((n ? n : 1) * sizeof(uint));
    mkList = (uint *)malloc(((size_t)n + 1) * sizeof(uint)); mkStamp = (uint *)calloc((size_t)numNodes + 1, sizeof(uint));
    if (!liveArc || !liveVert) { printf("Could not allocate memory.\n"); exit(1); }
    for (int i = 0; i < m; i++) liveArc[i] = i;
    for (int i = 0; i < n; i++) liveVert[i] = i;
    numLiveArc = m; numLiveVert = n;
    /* the incremental loop */
    ll css, qs;
    measureS(&css, &qs);
    ll bestLambda = currLambda;
    copySourceSet(css, qs);
    int iteration = 0;
    printf("c Iteration %d\n", iteration++);
    printf("c Computing mincut for lambda = %.*lf\n", DECIMALS, (double)currLambda / APP_VAL);
    solve();
    measureS(&css, &qs);
    ll val = css - currLambda * qs;
    printf("C(S,S) - lambda * q(S) = %lf\n", (double)val / APP_VAL);
    while (val > 0)
    {
        printf("c Iteration %d\n", iteration++);
        currLambda = ceil_div(css, qs);
        if (currLambda > bestLambda) { bestLambda = currLambda; copySourceSet(css, qs); }
        printf("c Updating capacities for lambda = %.*lf\n", DECIMALS, (double)currLambda / APP_VAL);
        updateCapacities();
        solve();
        measureS(&css, &qs);
        val = css - currLambda * qs;
        printf("C(S,S) - lambda * q(S) = %lf\n", (double)val / APP_VAL);
    }
    if (val < -TOL) printf("c ERROR: value is negative\n");
    if (qs != 0) { currLambda = css / qs; bestLambda = (ll)fmax_((double)currLambda, (double)bestLambda); }
    printf("\n");
    printf("c Optimal solution found: density* = %.*lf\n", DECIMALS, (double)bestLambda / APP_VAL);
    if (valuedNodes) printf("c C(S, S) + U(S) = %lld, q(S) = %lld\n", bestCSS / APP_VAL, bestQS);
    else printf("c C(S, S) = %lld, q(S) = %lld\n", bestCSS / APP_VAL, bestQS);
    if (dumpSourceSetFile)
    {
        for (int i = 0; i < n; i++) if (bestSourceSet[i]) fprintf(dumpSourceSetFile, "%d\n", i + 1);
        fclose(dumpSourceSetFile);
    }
    else
    {
        printf("\n");
        printf("c To dump the list of nodes in the densest subgraph into\n");
        printf("c a file, use option \"--dumpDensest FILE\"\n");
    }
    return 0;
}
