# Variable-occurrence bounds for CSP instances

Let $F$ be a CSP instance with $|F|$ constraints, $n$ distinct occurring variables and $L$ total variable occurrences (the sum of the scope lengths). If every scope is nonempty then $|F| \le L$, and if every variable occurs at most $\Delta$ times then $L \le \Delta n$. Hence instances with nonempty scopes and bounded occurrence have $O(n)$ constraints, which is the setting of sparse-instance arguments such as sparsification and bounded-occurrence reductions.

## Proof sketch

Count occurrences by constraints and by variables.

## Depends on

- [Finite-domain constraint satisfaction problems](finite-domain-constraint-satisfaction.md)

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
