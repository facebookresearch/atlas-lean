# Layered semi-unbounded circuits and proof trees

A *semi-unbounded* Boolean circuit has AND gates of fan-in at most two and OR gates of unbounded fan-in, with negations only at the inputs; it is *layered* if every child of a gate lies in the next layer. $\mathsf{SAC}^i$ is the class of languages with polynomial-size semi-unbounded circuits of depth $O(\log^i n)$ (non-uniform; the log-space uniform version is written the same way when uniformity is meant).

Fix an input. The *unfolding* of the circuit at a gate $g$ is the tree obtained by taking one copy of a gate for every path from $g$ to it, so that a gate shared by two branches occurs twice. A *proof tree* of $g$ is a subtree $T$ of the unfolding rooted at $g$ such that every OR occurrence in $T$ has exactly one child occurrence in $T$, every AND occurrence has all of its (at most two) child occurrences in $T$, and every leaf of $T$ is an input literal, or the constant $1$, that is true on the input. A gate is true iff it has a proof tree. Because the tree lives in the unfolding, the two branches of an AND gate may both use the same lower gate, possibly through different proof trees of it.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000 (Section 3, certificates as depth-first traversals of the subcircuit below a gate).
