# LR(1) grammars

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; sentential forms are words over $T \cup N$. Here $\Rightarrow_{\mathrm{rm}}^*$ denotes rightmost derivation (the reflexive-transitive closure of rightmost steps, each rewriting the rightmost nonterminal). For a sentential form $\pi$ and a lookahead $\ell$ (a terminal or the end of input), a reduce action at $\pi$ with lookahead $\ell$ by the handle $(\alpha, A, \beta)$ with right context $w \in T^*$ means: $\pi = \alpha\beta$, $S \Rightarrow_{\mathrm{rm}}^* \alpha A w$, $A \to \beta$ is a production of $g$, and $\ell$ is the first letter of $w$ ($\ell$ is the end of input if $w = \varepsilon$); and there is a shift action at $\pi$ with lookahead $\ell$ when $\ell$ is a terminal $a$ and $\pi a$ is a viable prefix (a prefix of $\alpha\beta$ for some $S \Rightarrow_{\mathrm{rm}}^* \alpha A w$ and production $A \to \beta$).

The grammar $g$ is LR(1) when, for every $\pi$ and $\ell$:

1. (no reduce/reduce conflict) if there are reduce actions at $\pi$ with lookahead $\ell$ by handles $(\alpha_1, A_1, \beta_1)$ and $(\alpha_2, A_2, \beta_2)$, with any right contexts, then $\alpha_1 = \alpha_2$, $A_1 = A_2$ and $\beta_1 = \beta_2$;
2. (no shift/reduce conflict) if there is a reduce action at $\pi$ with lookahead $\ell$, then there is no shift action at $\pi$ with lookahead $\ell$.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
