# The LL(1) predictive parser

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$. Let $M[A, \cdot]$ be the LL(1) table entry, defined through FIRST and FOLLOW sets.

The predictive parser $\mathrm{parse}(k, \gamma, w) \in \{\mathrm{true}, \mathrm{false}\}$, for a step budget $k \in \mathbb{N}$, a stack $\gamma$ (a sentential form, top first) and a remaining input $w \in T^*$, is defined by recursion on $k$:

- $\mathrm{parse}(0, \gamma, w) = \mathrm{false}$;
- $\mathrm{parse}(k+1, \varepsilon, \varepsilon) = \mathrm{true}$ and $\mathrm{parse}(k+1, \varepsilon, b w) = \mathrm{false}$;
- $\mathrm{parse}(k+1, a \gamma, \varepsilon) = \mathrm{false}$ for a terminal $a$;
- $\mathrm{parse}(k+1, a \gamma, b w) = \mathrm{parse}(k, \gamma, w)$ if $a = b$, and $\mathrm{false}$ otherwise;
- $\mathrm{parse}(k+1, A \gamma, w) = \mathrm{parse}(k, \alpha \gamma, w)$ if the table entry for $A$ and the first letter of $w$ (the end of input if $w = \varepsilon$) is the production $A \to \alpha$, and $\mathrm{false}$ if that entry is empty.

So the parser accepts exactly when the stack and the input become empty together within the step budget.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
