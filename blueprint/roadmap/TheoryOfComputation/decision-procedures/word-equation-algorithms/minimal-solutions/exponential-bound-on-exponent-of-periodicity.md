# Exponential bound on the exponent of periodicity

In a length-minimal solution of a word equation of size $n$, no nonempty word repeats more than $2^{cn}$ times in a row, for a constant $0 < c < 2$; this is the Kościelski–Pacholski bound, and an exponential bound is optimal.

There is a constant $c$ with $0 < c < 2$ such that the following holds. Let $U = V$ be a word equation over a finite alphabet with $n = |U| + |V|$, and let $\sigma$ be a length-minimal (nonerasing) solution. If $w^\ell$ is a factor of $\sigma(U)$ for some nonempty word $w$, then

$$
\ell \le 2^{cn} .
$$

Equivalently, every word equation of size $n$ that has a nonerasing solution has [exponent of periodicity](exponent-of-periodicity.md) at most $2^{cn}$. The bound concerns length-minimal solutions only: a non-minimal solution can have arbitrarily large exponent of periodicity, as in $X = X$.

## Depends on

- [Length-minimal solution of a word equation](length-minimal-solution.md)
- [Exponent of periodicity](exponent-of-periodicity.md)

## Proof depends on

- [p-stable normal form of a word](p-stable-normal-form.md)
- [Size of minimal natural solutions of linear Diophantine systems](minimal-solutions-of-linear-diophantine-systems.md)

## Expansion

This page becomes ready once the following proof step, due to A. Kościelski and L. Pacholski (Journal of the ACM 43 (1996)), is a page of its own: writing the values of a length-minimal solution in $p$-stable normal forms for a primitive word $p$ with $p^\ell$ a factor of the solution word, and reading the exponents of $p$ as unknowns, the equation yields a system of linear Diophantine equations with positivity constraints whose coefficients and constants are bounded linearly in $n$, such that every natural solution of the system yields a solution of the word equation and the length-minimal solution yields a minimal solution of the system.

With that step, the bound on minimal solutions of linear Diophantine systems bounds every exponent by a single exponential in $n$; the constant $c < 2$ comes from the specific counts of the Kościelski–Pacholski system. Diekert's report proves the same type of bound in full, for solutions of minimal length that also satisfy regular constraints, with the explicit system described in its proof of Theorem 3.2. The recompression method gives an independent but weaker estimate (Jeż, Section 8, Theorem 5), proved by tracking the single-letter exponent along the solutions met in a run, which need not all be length-minimal; it is not the route followed here.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Lemma 1 (Section 2), which states the bound with $0 < c < 2$ for length-minimal solutions, citing Kościelski and Pacholski; Section 1 for optimality; Section 8 for the description of the original proof and for Theorem 5
- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Theorem 3.2 and its proof (Section 3)
