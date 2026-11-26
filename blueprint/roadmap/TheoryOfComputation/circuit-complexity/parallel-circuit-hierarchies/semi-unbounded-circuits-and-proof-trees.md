# Layered semi-unbounded circuits and proof trees

A *semi-unbounded* Boolean circuit has AND gates of fan-in at most two and OR gates of unbounded fan-in, with negations only at the inputs; it is *layered* if every child of a gate lies in the next layer. $\mathsf{SAC}^i$ is the class of languages with polynomial-size semi-unbounded circuits of depth $O(\log^i n)$. A *proof tree* of a gate on an input is a minimal subtree certifying that the gate evaluates to $1$: at an OR gate it selects one true child, at an AND gate both children; a gate is true iff it has a proof tree.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000.
