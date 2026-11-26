# Rightmost derivations

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; sentential forms are words over $T \cup N$.

Rightmost derivability $u \Rightarrow_{\mathrm{rm}}^* v$ is the reflexive-transitive closure of the rightmost step relation: $u \Rightarrow_{\mathrm{rm}} v$ holds when $u = p A q$ and $v = p \beta q$ for a production $A \to \beta$ of $g$ and a word $q$ of terminals. Thus $u \Rightarrow_{\mathrm{rm}}^* v$ when $v$ arises from $u$ by finitely many (possibly zero) rightmost steps.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
