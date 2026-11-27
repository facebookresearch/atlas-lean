# Auxiliary pushdown automata and LogCFL

An **auxiliary pushdown automaton** is a nondeterministic Turing machine with a read-only input tape, finitely many work tapes and one unbounded pushdown stack, whose stack is not charged to its space. For bounds $s,t$, $\mathsf{AuxPDA}(s,t)$ is the class of languages decided by such machines using $O(s(n))$ work cells and halting on every branch within $O(t(n))$ steps. $\mathsf{LogCFL}=\mathsf{AuxPDA}(\log n, n^{O(1)})$ (Sudborough's characterization of the closure of the context-free languages under logspace reductions); its unambiguous version $\mathsf{UAuxPDA}$ requires exactly one accepting branch on members and none on non-members. One has $\mathsf{UL}\subseteq\mathsf{UAuxPDA}\subseteq\mathsf{LogCFL}$, the first inclusion by an unused stack (an unambiguous logspace machine all of whose branches halt runs in polynomial time). Whether $\mathsf{NL}=\mathsf{UL}$ is open; Reinhardt and Allender prove the nonuniform collapses $\mathsf{NL}/\mathrm{poly}=\mathsf{UL}/\mathrm{poly}$ and $\mathsf{LogCFL}/\mathrm{poly}=\mathsf{UAuxPDA}/\mathrm{poly}$.

## Depends on

- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)
- [Unambiguous space classes USPACE and UL](unambiguous-space-classes.md)

## Sources

- Ivan Hal Sudborough, "On the Tape Complexity of Deterministic Context-Free Languages", Journal of the ACM 25(3), 1978.
- Klaus Reinhardt and Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
