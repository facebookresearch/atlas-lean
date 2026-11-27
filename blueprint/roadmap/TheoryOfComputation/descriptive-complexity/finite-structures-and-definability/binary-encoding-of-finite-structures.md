# Binary encoding of finite relational structures

Fix a finite relational vocabulary with an enumeration $R_1,\dots,R_s$ of its symbols. A finite structure $\mathfrak{A}$ with universe numbered as $\{0,\dots,n-1\}$ is encoded as the bit string $0^n 1$ followed by, for each $R_i$ of arity $r_i$ in turn, its truth table listing the values of $R_i$ on the $n^{r_i}$ tuples in lexicographic (base-$n$) order (a nullary symbol contributes one bit, also for $n = 0$). The encoding has length exactly $n + 1 + \sum_{i=1}^{s} n^{r_i}$, which for $n \ge 1$ is at most $(s+1)\,n^{r} + 1$ with $r = \max(1, r_1, \dots, r_s)$, a polynomial in $n$ fixed by the vocabulary. Well-formedness of a string and reading a table entry are polynomial-time computable.

## Depends on

- [Finite relational structures are determined by their atomic facts](finite-structures-from-atomic-facts.md)
- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004, Section 6.1 (the encoding $0^n 1 \cdot \mathrm{enc}(R_1) \cdots \mathrm{enc}(R_s)$).
