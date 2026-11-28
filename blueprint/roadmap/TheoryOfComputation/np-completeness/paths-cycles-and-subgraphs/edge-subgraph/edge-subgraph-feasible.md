# Feasible EDGE-SUBGRAPH instances

An EDGE-SUBGRAPH instance $(n, E, K)$ is feasible when some sublist $E'$ of the edge list has at least $K$ **entries** and the following graph is a line graph: form the simple graph on the vertices $0, \dots, n-1$ from the entries of $E'$, discarding loops and pairs with an endpoint out of range and identifying repeated and reversed pairs, and restrict it to its non-isolated vertices. An out-of-range pair counts toward $K$ without contributing an edge.
