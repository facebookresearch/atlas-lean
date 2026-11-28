# Some context-free language is not deterministic

A language $L$ over an alphabet $T$ is deterministic context-free when some deterministic pushdown automaton with finitely many states and stack symbols, whose transitions read only letters from a finite subset of $T \cup \{\dashv\}$, accepts by empty stack exactly the words $w\dashv$ with $w \in L$, where $\dashv$ is an end marker.

The following holds: there is a language $L$ over the two-letter alphabet $\{0, 1\}$ that is context-free but not deterministic context-free.

## Sources

- S. Ginsburg and S. Greibach, "Deterministic context free languages", *Information and Control* 9 (1966), 620-648.
