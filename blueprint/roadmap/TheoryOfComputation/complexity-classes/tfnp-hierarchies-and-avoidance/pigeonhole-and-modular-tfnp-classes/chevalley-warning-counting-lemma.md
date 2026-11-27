# Chevalley–Warning lemma: the zero count mod p equals ± the number of max-degree monic monomials

For every prime $p$ and every $\mathbf f\in\mathbb F_p[x_1,\dots,x_n]^m$,

$$
|\mathcal V_{\mathbf f}|\equiv(-1)^n\cdot\#\{\text{max-degree monic monomials of }\mathrm{CW}_{\mathbf f}\}\pmod p .
$$

In particular, if $\sum_i\deg f_i<n$ then no monic monomial of $\mathrm{CW}_{\mathbf f}$ reaches degree $n(p-1)$, so $|\mathcal V_{\mathbf f}|\equiv0\pmod p$ (the Chevalley–Warning theorem), and every syntactically refutable condition implying that the max-degree monic monomials cancel modulo $p$ (a "proof of cancellation") yields a total search problem in $\mathsf{PPA}_p$.

## Proof sketch

By Fermat, $\mathrm{CW}_{\mathbf f}(x)=1$ if $x\in\mathcal V_{\mathbf f}$ and $0$ otherwise, so $|\mathcal V_{\mathbf f}|\equiv\sum_{x\in\mathbb F_p^n}\mathrm{CW}_{\mathbf f}(x)$. Expand $\mathrm{CW}_{\mathbf f}$ into monic monomials with exponents at most $p-1$. Since $\sum_{t\in\mathbb F_p}t^a$ is $0$ for $0\le a\le p-2$ (with $0^0=1$) and $-1$ for $a=p-1$, a monomial $\prod_jx_j^{a_j}$ sums to $0$ over $\mathbb F_p^n$ unless all $a_j=p-1$, when it sums to $(-1)^n$. Summing over the expansion gives the claim.

## Depends on

- [CHEVALLEY_p, GENERAL-CHEVALLEY_p and CHEVALLEY-WITH-SYMMETRY_p: explicit search problems from the Chevalley–Warning theorem](chevalley-search-problems.md)
- [The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes](ppa-q-and-the-and-operator.md)

## Proof depends on

- [Chevalley–Warning theorem, existence form](../../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-ne-common-zero.md)

## Sources

- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
