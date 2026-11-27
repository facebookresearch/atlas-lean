# Venkateswaran: polynomial-time auxiliary pushdown automata compile into SAC^1 circuits

Every language accepted by a nondeterministic logarithmic-space auxiliary pushdown automaton running in polynomial time (the class $\mathsf{LOGCFL}$) has polynomial-size layered semi-unbounded circuits of logarithmic depth; that is, $\mathsf{LOGCFL}\subseteq\mathsf{SAC}^1$ for the non-uniform $\mathsf{SAC}^1$ of the linked page. Venkateswaran's circuits are log-space uniform, and log-space uniform $\mathsf{SAC}^1$ equals $\mathsf{LOGCFL}$; the non-uniform class is larger, $\mathsf{LOGCFL}/\mathrm{poly}$, so equality holds only in the uniform setting. The circuit's gates assert realizability of surface-configuration pairs, and the construction balances the depth by splitting a realizable computation at a middle pair of matching push and pop moves.

## Proof sketch

Gates represent statements 'surface configuration $C$ reaches $D$ with the same stack height'; such a statement holds iff it is a single step, a concatenation of two shorter such statements, or a push–(statement)–pop sandwich. Choosing splits that halve the length gives logarithmic depth with OR gates over the polynomially many intermediate configurations and binary AND gates.

## Depends on

- [Layered semi-unbounded circuits and proof trees](semi-unbounded-circuits-and-proof-trees.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Sources

- H. Venkateswaran, "Properties that Characterize LOGCFL", Journal of Computer and System Sciences 43(2), 1991.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000 (Proposition 3.1).
