# LL(1) grammars

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$. FIRST, FOLLOW and nullability are as defined through derivations.

The grammar $g$ is LL(1) when for every nonterminal $A$ and every two distinct productions $A \to \alpha$ and $A \to \beta$ of $g$:

1. $\mathrm{FIRST}(\alpha) \cap \mathrm{FIRST}(\beta) = \emptyset$;
2. if $\alpha$ is nullable, then $\mathrm{FIRST}(\beta) \cap \mathrm{FOLLOW}(A) = \emptyset$, and if $\beta$ is nullable, then $\mathrm{FIRST}(\alpha) \cap \mathrm{FOLLOW}(A) = \emptyset$;
3. $\alpha$ and $\beta$ are not both nullable.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
