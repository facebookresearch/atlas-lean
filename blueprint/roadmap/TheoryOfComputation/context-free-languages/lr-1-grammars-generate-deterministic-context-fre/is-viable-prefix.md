# Viable prefixes

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; sentential forms are words over $T \cup N$. Here $\Rightarrow_{\mathrm{rm}}^*$ denotes rightmost derivation (the reflexive-transitive closure of rightmost steps, each rewriting the rightmost nonterminal).

A sentential form $\pi$ is a viable prefix of $g$ when there are a sentential form $\alpha$, a nonterminal $A$, a production $A \to \beta$ of $g$ and a terminal word $w$ with $S \Rightarrow_{\mathrm{rm}}^* \alpha A w$ such that $\pi$ is a prefix of $\alpha\beta$ (that is, $\alpha\beta = \pi\rho$ for some $\rho$).

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
