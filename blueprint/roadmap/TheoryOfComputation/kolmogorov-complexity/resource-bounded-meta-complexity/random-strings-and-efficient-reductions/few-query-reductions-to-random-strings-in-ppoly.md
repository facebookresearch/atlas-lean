# Decidable sets with few-query truth-table reductions to R_C are in P/poly

If a decidable set reduces to the random strings $R_C$ by a polynomial-time truth-table reduction with $f(n)$ queries, it has polynomial-time algorithms with about $2^{3f(n)\log f(n)}$ bits of advice. So $O(\log n/\log\log n)$ queries give only P/poly, and $n^{\alpha}$ queries with $\alpha<1$ cannot reach every decidable set.

1. If $A$ is recursive and reduces to $R_C$ via a polynomial-time $f(n)$-truth-table reduction, then $A\in\mathrm{P}/\bigl(f(n)\,2^{3f(n)\log f(n)}\bigr)$.
2. If $A$ is recursive and reduces to $R_C$ via a polynomial-time truth-table reduction with $O(\log n/\log\log n)$ queries, then $A\in\mathrm{P}/\mathrm{poly}$.
3. If $g(n)2^{3g(n)\log g(n)}<2^n$, there is a recursive set that does not reduce to $R_C$ via a polynomial-time $g(n)$-truth-table reduction. In particular, for every $\alpha<1$ some recursive set has no polynomial-time $n^\alpha$-truth-table reduction to $R_C$.

## Expansion

Drop all queries of length at least $s_n=2\log f(n)+2\log\log f(n)+c$. There are fewer than $2^{3f(n)\log f(n)}$ possible sets of remaining short queries; for each one the advice records one answer vector of $f(n)$ bits, and long queries are answered "not random". If no correct answer vector existed for some class of inputs, a program could find the first bad input from the class and the count of random short queries, enumerate the complement of $R_C$ to recover the answers, and thereby describe a long random query in fewer than $s_n$ bits, a contradiction. Item 3 uses recursive languages outside $\mathrm{P}/(2^n-1)$.

## Depends on

- [Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}](kolmogorov-random-strings.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman and Michal Koucký, "What Can Be Efficiently Reduced to the Kolmogorov-Random Strings?", *Annals of Pure and Applied Logic* 138, 2006, [doi:10.1016/j.apal.2005.05.013](https://doi.org/10.1016/j.apal.2005.05.013) (Theorem 8, Corollaries 9 and 10; numbering of the ECCC TR04-044 version).
