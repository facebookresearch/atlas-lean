# Meyer: P/poly = P^SPARSE = P^TALLY

For every language $A$ the following are equivalent: (i) $A\in\mathsf{P}/\mathrm{poly}$; (ii) $A\in\mathsf{P}^{S}$ for some sparse $S$; (iii) $A\in\mathsf{P}^{T}$ for some tally $T$; (iv) $A$ is polynomial-time truth-table reducible to a tally language. Thus $\mathsf{P}/\mathrm{poly}=\mathsf{P}^{\mathsf{SPARSE}}=\mathsf{P}^{\mathsf{TALLY}}$.

## Proof sketch

From advice $(\alpha_n)$ build the tally set $T=\{1^{\langle n,i\rangle}: \text{the }i\text{-th bit of }\alpha_n\text{ is }1\}$ and read the advice with non-adaptive queries. Conversely, a polynomial-time oracle machine queries only strings of length $\le p(n)$, and the polynomially many such members of a sparse oracle form polynomial advice.

## Depends on

- [Polynomial time with polynomial advice](../../time-and-space-complexity-classes/ppoly.md)
- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [Sparse decision problems](../../mahaney-s-theorem/sparse.md)
- [Tally languages](tally-languages.md)
- [Polynomial-time truth-table, bounded and Turing reductions](../reducibilities-and-isomorphism/truth-table-reductions.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Lane A. Hemaspaandra and Leen Torenvliet, "Theory of Semi-Feasible Algorithms", Springer, 2003.
