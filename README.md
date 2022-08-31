# TGFD Discovery
*Partition:*
Get all vertex and their frequency and then get all edges and their weight

Global logic to assign vertex to machine, each time assign one vertex to one machine

Each time select next vertex based on neighbour and histogram, each time select next machine in a cycle way

To keep workload balance and less missing edges, which means the workload on each machine should be close to each other and bonded vertices should be together

Get a list of vertex type on each machine for further usage. 

*vSpawn:*
Then do stats on graph to get histogram for vertex and edge

vSpawn will use histogram to generate pattern and extend pattern

Once get a pattern, use this pattern to do partial match for all vertices on each machine

*Matching:*
A match is a set of constant literal

Before doing partial match, need to determine a new centre vertex on each machine, because the match is based on extension of centre vertex

Get distance between centre vertex of original pattern and vertex on each machine, then select the closet one as new centre vertex

Get match of the centre vertex firstly, then use the matches to find match for partial pattern

Use isomorphism to decide if two patterns have the same structure to get further match

*hSpawn:*
Generate attribute dependency from literalTree by using literals

A dependency for a pattern is a literal path

It relies on the stats of the whole graph and a pattern

