# The class MA (Merlin–Arthur)

A decision problem $L$ is in $\mathsf{MA}$ when there are
polynomials $p$ and $q$ with natural-number coefficients and a polynomial-time computable
predicate $R$ on triples $(x, w, r)$ of bitstrings such that, for every bitstring $x$, with
$N_x(w)$ the number of strings $r$ of length $p(|x|)$ for which $R(x, w, r)$ is true: if $L(x)$
is true, then some $w$ with $|w| \le q(|x|)$ satisfies $3 N_x(w) \ge 2 \cdot 2^{p(|x|)}$; and if
$L(x)$ is false, then every $w$ with $|w| \le q(|x|)$ satisfies $3 N_x(w) \le 2^{p(|x|)}$.

So Merlin sends a witness $w$ first and Arthur then flips $p(|x|)$ coins $r$: Arthur accepts
with probability at least $2/3$ for some $w$ on yes-instances, and with probability at most
$1/3$ for every $w$ on no-instances. In the class AM the random string comes before the
witness.

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 8.1; L. Babai, "Trading group theory for randomness", Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing (STOC 1985), 421-429.
