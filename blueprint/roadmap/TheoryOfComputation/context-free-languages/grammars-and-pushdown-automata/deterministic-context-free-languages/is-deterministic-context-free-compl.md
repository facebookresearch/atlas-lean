# Deterministic context-free languages are closed under complement

A language $L$ over an alphabet $T$ is deterministic context-free when some deterministic pushdown automaton with finitely many states and stack symbols, whose transitions read only letters from a finite subset of $T \cup \{\dashv\}$, accepts by empty stack exactly the words $w\dashv$ with $w \in L$, where $\dashv$ is an end marker.

The following holds. Let $T$ be a finite alphabet and $L \subseteq T^*$ a deterministic context-free language. Then its complement $T^* \setminus L$ is deterministic context-free.

The finiteness of $T$ matters: over $T = \mathbb{N}$ the empty language is deterministic context-free, but its complement is not.

## Sources

- S. Ginsburg and S. Greibach, "Deterministic context free languages", *Information and Control* 9 (1966), 620-648.
