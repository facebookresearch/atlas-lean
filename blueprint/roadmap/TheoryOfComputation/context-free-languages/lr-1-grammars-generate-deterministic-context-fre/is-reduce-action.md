# Reduce actions of an LR(1) parser

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; sentential forms are words over $T \cup N$. Here $\Rightarrow_{\mathrm{rm}}^*$ denotes rightmost derivation (the reflexive-transitive closure of rightmost steps, each rewriting the rightmost nonterminal). Let $\pi$ be a sentential form and $\ell$ a lookahead (a terminal or the end of input).

A reduce action at $\pi$ with lookahead $\ell$ by the handle $(\alpha, A, \beta)$ with right context $w \in T^*$ means: $\pi = \alpha\beta$, $S \Rightarrow_{\mathrm{rm}}^* \alpha A w$, $A \to \beta$ is a production of $g$, and $\ell$ is the first letter of $w$ ($\ell$ is the end of input if $w = \varepsilon$).

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
