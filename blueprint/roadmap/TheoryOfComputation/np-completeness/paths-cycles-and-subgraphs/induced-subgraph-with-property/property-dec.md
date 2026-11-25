# Recognizing a graph property

For a graph property $\Pi$, this decision problem accepts a bitstring $x$ exactly when $x$
decodes to a pair $(n, E)$ such that $E$ is a [simple edge list](simple-edge-list.md) on $\{0,
\dots, n-1\}$ and the graph with vertices $0, \dots, n-1$ and edges $E$ has property $\Pi$. It
rejects every bitstring that does not decode to such a pair.
