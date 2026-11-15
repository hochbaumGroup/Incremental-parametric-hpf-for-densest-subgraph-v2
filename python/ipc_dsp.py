"""Python interface to the IPC-DSP executable (Incremental Parametric Cut procedure for the
densest subgraph problem). Compile the executable first (`mkdir bin; make`)."""
import os
import subprocess
import tempfile

EXECUTABLE = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "bin", "IPC-DSP")


def densest_subgraph(G, edge_weight=None, node_weight=None, node_value=None, accuracy=4, executable=EXECUTABLE):
    """Find a subset S of the nodes of the undirected networkx graph G that maximizes
    (sum of the weights of the edges inside S + sum of the values of the nodes of S) / (sum of the
    weights of the nodes of S).

    edge_weight, node_weight, node_value: names of the attributes that hold the edge weights (positive
    integers, default 1), the node weights (positive integers, default 1) and the node values (integers
    of any sign, default 0). `accuracy` is the number of decimal places of the density.

    Returns (density, nodes), where `nodes` is the list of the nodes of S."""
    if G.is_directed() or G.is_multigraph():
        raise TypeError("Graph should be an undirected networkx Graph.")
    names = list(G.nodes())
    index = {v: i + 1 for i, v in enumerate(names)}
    edges = [(u, v, d) for u, v, d in G.edges(data=True) if u != v]
    lines = ["%d %d" % (len(names), len(edges))]
    options = ["--accuracy", str(int(accuracy))]
    if node_weight or node_value:
        for v in names:
            fields = []
            if node_weight:
                fields.append(str(int(G.nodes[v][node_weight])))
            if node_value:
                fields.append(str(int(G.nodes[v][node_value])))
            lines.append(" ".join(fields))
    for u, v, d in edges:
        a, b = sorted((index[u], index[v]))
        lines.append("%d %d" % (a, b) + (" %d" % int(d[edge_weight]) if edge_weight else ""))
    if node_weight:
        options.append("--weightedNodes")
    if node_value:
        options.append("--valuedNodes")
    if edge_weight:
        options.append("--weightedEdges")
    with tempfile.TemporaryDirectory() as tmp:
        dump = os.path.join(tmp, "densest.txt")
        run = subprocess.run([executable] + options + ["--dumpDensest", dump], input="\n".join(lines) + "\n",
                             capture_output=True, text=True, check=True)
        with open(dump) as f:
            nodes = [names[int(x) - 1] for x in f.read().split()]
    for line in run.stdout.splitlines():
        if line.startswith("c Optimal solution found: density* ="):
            return float(line.split("=")[1]), nodes
    raise RuntimeError("IPC-DSP did not report a solution:\n" + run.stdout)
