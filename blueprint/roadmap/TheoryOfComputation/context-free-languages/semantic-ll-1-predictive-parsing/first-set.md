# FIRST sets of sentential forms

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$.

The FIRST set of a sentential form $\alpha$ is the set of terminals that can begin a terminal word derived from $\alpha$:

$$\mathrm{FIRST}(\alpha) = \{\, a \in T : \alpha \Rightarrow^* a u \text{ for some } u \in T^* \,\}.$$

It is defined through derivations, not as the result of a fixpoint computation.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
