# The canonical total search problems LOCALOPT, PIGEON, END-OF-LINE, SINK-OF-LINE and LEAF

Inputs are Boolean circuits on $n$ input bits.

- **LOCALOPT**: given $S:\{0,1\}^n\to\{0,1\}^n$ and $V:\{0,1\}^n\to\mathbb{N}$, find $x$ with $V(S(x))\le V(x)$.
- **PIGEON**: given $C:\{0,1\}^n\to\{0,1\}^n$, find $x$ with $C(x)=0^n$ or $x\ne y$ with $C(x)=C(y)$.
- **END-OF-LINE**: given predecessor and successor circuits $P,S$, consider the graph with arcs $x\to S(x)$ whenever $P(S(x))=x$; every vertex has in- and out-degree at most $1$, a *source* has in-degree $0$ and out-degree $1$, and a *sink* in-degree $1$ and out-degree $0$. If $0^n$ is not a source, $0^n$ is a solution; otherwise find a sink or a source $x\ne0^n$.
- **SINK-OF-LINE**: the same graph; $0^n$ is a solution if it is not a source, and otherwise only a sink is.
- **LEAF**: given a circuit listing at most two neighbours of each vertex of an undirected graph (an edge joins two vertices that list each other), find $0^n$ if it does not have degree $1$, and otherwise another vertex of degree $1$.

Each problem is total by an elementary principle (well-foundedness of a potential, the pigeonhole principle, parity/degree counting; when $0^n$ is a source, the path leaving it ends in a sink), hence lies in $\mathsf{TFNP}$.

## Depends on

- [Search problems: FNP, FP and TFNP](../search-problems-fnp-fp-and-tfnp.md)
- [The END-OF-THE-LINE graph](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/adj.md)
- [The class PLS of polynomial local search problems](../the-class-pls-of-polynomial-local-search.md)

## Sources

- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences 48(3), 1994.
- Paul Beame et al., "The Relative Complexity of NP Search Problems", Journal of Computer and System Sciences 57(1), 1998.
- David S. Johnson, Christos H. Papadimitriou and Mihalis Yannakakis, "How Easy Is Local Search?", Journal of Computer and System Sciences 37(1), 1988.
