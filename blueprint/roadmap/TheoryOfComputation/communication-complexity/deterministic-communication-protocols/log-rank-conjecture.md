# The log-rank conjecture (open)

A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. The deterministic communication complexity $D(f)$ is the least depth of a protocol computing $f$, and $0$ if no protocol computes $f$. For a field $K$, the communication matrix $M_f$ of $f$ over $K$ is the $X \times Y$ matrix with entry $1$ at $(x, y)$ if $f(x, y) = 1$ and $0$ otherwise. The log-rank conjecture is the statement that there is a constant $C \in \mathbb{N}$
such that for all finite sets $X$ and $Y$ and every $f : X \times Y \to \{0, 1\}$,

$$D(f) \le C \left(\log_2 \operatorname{rank}_{\mathbb{R}} M_f + 1\right)^C,$$

where $M_f$ is the communication matrix of $f$ over $\mathbb{R}$ and $\log_2 0$ is taken to be $0$. It is an open problem.

The additive $1$ and the factor $C$ make the statement meaningful for matrices of rank one, which can need
one bit of communication.

## Background

- [Log-rank lower bound](log-rank-le-comm-complexity.md): the inequality $\log_2 \operatorname{rank} M_f \le D(f)$, which the conjecture would match up to a polynomial.

## Sources

- L. Lovász and M. Saks, "Lattices, Möbius functions and communication complexity", *29th Annual Symposium on Foundations of Computer Science (FOCS 1988)*.
- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Conjecture 2.12, stated there as $D(M) \le \log^{\alpha} \operatorname{rank}(M)$.
