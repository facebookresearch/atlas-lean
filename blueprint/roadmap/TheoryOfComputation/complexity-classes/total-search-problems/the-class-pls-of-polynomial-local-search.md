# The class PLS of polynomial local search problems

A problem in $\mathsf{PLS}$ is given by a polynomial $p$, a polynomial-time recognizable set of instances, for each instance $x$ a set $F(x) \subseteq \{0,1\}^{\le p(|x|)}$ of feasible solutions with polynomial-time membership, and three polynomial-time algorithms: $A$ outputs some $s_0 \in F(x)$; $B$ computes an integer cost $c(x, s)$ for $s \in F(x)$; and $C$, given $s \in F(x)$, outputs either "locally optimal" or a neighbour $s' \in F(x)$ with strictly better cost. The task is to find a locally optimal $s \in F(x)$, one on which $C$ reports no improvement. Every $\mathsf{PLS}$ problem is total, since iterating $C$ from $A(x)$ strictly improves the cost over a finite set, so $\mathsf{PLS} \subseteq \mathsf{TFNP}$. A PLS-reduction from $P$ to $Q$ is a pair of polynomial-time maps $f$, $g$ such that $f$ maps instances of $P$ to instances of $Q$ and $g(x, \cdot)$ maps every local optimum of $f(x)$ to a local optimum of $x$.

## Depends on

- [Search problems: FNP, FP and TFNP](search-problems-fnp-fp-and-tfnp.md)

## Sources

- Original definition: D. S. Johnson, C. H. Papadimitriou and M. Yannakakis, "How easy is local search?", *Journal of Computer and System Sciences* 37(1):79–100, 1988. The formulation follows Roughgarden, Lecture 19, Section 2, which credits it to them.
- T. Roughgarden, *Stanford CS364A Algorithmic Game Theory*, Lecture 19, 2013, <https://theory.stanford.edu/~tim/f13/l/l19.pdf>, Section 2
