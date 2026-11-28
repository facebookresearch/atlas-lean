# Rightmost derivation steps

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; sentential forms are words over $T \cup N$.

A sentential form $u$ rewrites to $v$ in one rightmost step, $u \Rightarrow_{\mathrm{rm}} v$, when there are a production $A \to \beta$ of $g$ and sentential forms $p, q$ with

$$u = p\, A\, q, \qquad v = p\, \beta\, q,$$

and every symbol of $q$ is a terminal. So the rewritten nonterminal is the rightmost nonterminal of $u$.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
