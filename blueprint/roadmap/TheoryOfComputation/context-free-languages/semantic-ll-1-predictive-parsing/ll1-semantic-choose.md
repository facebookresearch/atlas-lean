# The LL(1) table entry

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$. FIRST, FOLLOW and nullability are as defined through derivations.

For a nonterminal $A$ and a lookahead that is either a terminal $b$ or the end of input, the LL(1) table entry $M[A, \cdot]$ is defined as follows. Call a production $A \to \alpha$ of $g$ admissible

- for the lookahead $b$, if $b \in \mathrm{FIRST}(\alpha)$, or $\alpha$ is nullable and $b \in \mathrm{FOLLOW}(A)$;
- for the end of input, if $\alpha$ is nullable.

If some production of $A$ is admissible, the entry is one admissible production, chosen arbitrarily; otherwise the entry is empty. The entry is a mathematical choice, not the output of a table-construction algorithm.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
