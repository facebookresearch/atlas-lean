# Feasibility for DENSEST k-SUBGRAPH

An instance $(n, E, k, m)$ of DENSEST k-SUBGRAPH is
feasible when there are a finite set $S$ of exactly $k$ natural numbers, each less than $n$, and
a sublist $E'$ of $E$ (obtained by deleting entries and keeping the order) with at least $m$
entries such that both components of every pair in $E'$ lie in $S$.

For a well-formed instance this says that some $k$ vertices of the graph of $E$ on $n$ vertices
induce at least $m$ edges.
