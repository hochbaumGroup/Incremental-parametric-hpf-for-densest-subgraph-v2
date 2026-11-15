CFLAGS=-O4 -g -Wall
BINDIR=bin
SOURCES = src/2.0/IPC-DSP.c
OBJECTS = $(SOURCES:.c=.o)
TARGET = IPC-DSP
CC=gcc

all: $(TARGET) 

clean:
	rm -f $(OBJECTS) $(TARGET) 

$(TARGET): $(OBJECTS)
	$(CC) $(CFLAGS) -o bin/$(TARGET) $(OBJECTS)
