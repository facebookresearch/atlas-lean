# The LL(1) predictive parser

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$. The terminal alphabet $T$ has decidable equality, which the parser uses to match a terminal on the stack against the next input letter. The table entry for a nonterminal $A$ and a lookahead $b$ (a letter, or the end of input) is some production $A \to \alpha$ of $g$ with $b \in \mathrm{FIRST}(\alpha)$, or with $\alpha \Rightarrow^* \varepsilon$ and $b \in \mathrm{FOLLOW}(A)$ (for the end of input: with $\alpha \Rightarrow^* \varepsilon$), chosen by classical choice when one exists, and empty otherwise. Because FIRST, FOLLOW and nullability are stated through derivability, and the entry is picked by choice, the definition below is a semantic recurrence, not an executable parser.

The predictive parser $\mathrm{parse}(k, \gamma, w) \in \{\mathrm{true}, \mathrm{false}\}$, for a step budget $k \in \mathbb{N}$, a stack $\gamma$ (a sentential form, top first) and a remaining input $w \in T^*$, is defined by recursion on $k$:

- $\mathrm{parse}(0, \gamma, w) = \mathrm{false}$;
- $\mathrm{parse}(k+1, \varepsilon, \varepsilon) = \mathrm{true}$ and $\mathrm{parse}(k+1, \varepsilon, b w) = \mathrm{false}$;
- $\mathrm{parse}(k+1, a \gamma, \varepsilon) = \mathrm{false}$ for a terminal $a$;
- $\mathrm{parse}(k+1, a \gamma, b w) = \mathrm{parse}(k, \gamma, w)$ if $a = b$, and $\mathrm{false}$ otherwise;
- $\mathrm{parse}(k+1, A \gamma, w) = \mathrm{parse}(k, \alpha \gamma, w)$ if the table entry for $A$ and the first letter of $w$ (the end of input if $w = \varepsilon$) is the production $A \to \alpha$, and $\mathrm{false}$ if that entry is empty.

So the parser accepts exactly when the stack and the input become empty together within the step budget.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
