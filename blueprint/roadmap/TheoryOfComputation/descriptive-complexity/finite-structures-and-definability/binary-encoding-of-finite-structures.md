# Binary encoding of finite relational structures

Fix a finite relational vocabulary with an enumeration $R_1,\dots,R_s$ of its symbols. A finite structure $\mathfrak{A}$ with universe numbered as $\{0,\dots,n-1\}$ is encoded as the bit string consisting of $n$ in unary followed by, for each $R_i$ of arity $r_i$, its truth table listing the values of $R_i$ on the $n^{r_i}$ tuples in lexicographic (base-$n$) order. The encoding of a structure of size $n \ge 1$ has length at most $(s+1)(2n^{r} + 1)$ with $r$ the maximal arity, a polynomial in $n$ fixed by the vocabulary. Well-formedness of a string and reading a table entry are polynomial-time computable.

## Depends on

- [Finite relational structures are determined by their atomic facts](finite-structures-from-atomic-facts.md)
- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
