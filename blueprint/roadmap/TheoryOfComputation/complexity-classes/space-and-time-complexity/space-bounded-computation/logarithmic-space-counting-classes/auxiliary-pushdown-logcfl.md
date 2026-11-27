# Auxiliary pushdown automata and LogCFL

An **auxiliary pushdown automaton** is a nondeterministic Turing machine with a read-only input tape, finitely many work tapes and one unbounded pushdown stack, whose stack is not charged to its space. For bounds $s,t$, $\mathsf{AuxPDA}(s,t)$ is the class of languages decided by such machines using $O(s(n))$ work cells and halting on every branch within $O(t(n))$ steps. $\mathsf{LogCFL}=\mathsf{AuxPDA}(\log n, n^{O(1)})$ (Sudborough's characterization of the closure of the context-free languages under logspace reductions); its unambiguous version $\mathsf{UAuxPDA}$ requires exactly one accepting branch on members and none on non-members. One has $\mathsf{NL}\subseteq\mathsf{UAuxPDA}\subseteq\mathsf{LogCFL}$, the first inclusion by $\mathsf{NL}=\mathsf{UL}$ and an unused stack.

## Depends on

- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)
- [Unambiguous space classes USPACE and UL](unambiguous-space-classes.md)

## Sources

- Klaus Reinhardt and Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
