# LR(1) grammars generate deterministic context-free languages

Let $g$ be a context-free grammar over a terminal alphabet $T$ that is LR(1): at every viable prefix and one-letter lookahead, all reduce actions use the same handle and no reduce action coexists with a shift action. Then $L(g)$ is deterministic context-free: some deterministic pushdown automaton with finitely many states and stack symbols, whose transitions read only letters from a finite subset of $T \cup \{\dashv\}$, accepts by empty stack exactly the words $w\dashv$ with $w \in L(g)$, where $\dashv$ is an end marker.

## Sources

- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
