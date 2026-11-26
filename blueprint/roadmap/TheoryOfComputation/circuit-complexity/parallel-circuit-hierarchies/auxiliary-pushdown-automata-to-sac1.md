# Venkateswaran: polynomial-time auxiliary pushdown automata compile into SAC^1 circuits

Every language accepted by a nondeterministic logarithmic-space auxiliary pushdown automaton running in polynomial time (the class $\mathsf{LOGCFL}$) has polynomial-size layered semi-unbounded circuits of logarithmic depth; that is, $\mathsf{LOGCFL}\subseteq\mathsf{SAC}^1$ (indeed equality holds). The circuit's gates assert realizability of surface-configuration pairs, and the construction balances the depth by splitting a realizable computation at a middle pair of matching push and pop moves.

## Proof sketch

Gates represent statements 'surface configuration $C$ reaches $D$ with the same stack height'; such a statement holds iff it is a single step, a concatenation of two shorter such statements, or a push–(statement)–pop sandwich. Choosing splits that halve the length gives logarithmic depth with OR gates over the polynomially many intermediate configurations and binary AND gates.

## Depends on

- [Layered semi-unbounded circuits and proof trees](semi-unbounded-circuits-and-proof-trees.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000.
