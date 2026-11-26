# Linearized arithmetization has low degree

Let $\varphi = Q_1 x_1 \cdots Q_n x_n\, \psi$ be a closed prenex quantified Boolean formula with a matrix $\psi$ of size $m$. Inserting a linearization operator $L_{x_j}$ for every free variable $x_j$ after each quantifier yields an arithmetic expression whose intermediate polynomials all have degree at most $2$ in each variable after a quantifier and at most $m$ initially, and whose value is $1$ if $\varphi$ is true and $0$ otherwise. This degree bound is what makes the sum-check style interactive proof of $\mathrm{IP} = \mathrm{PSPACE}$ run with polynomially many rounds over a field of polynomial size.

## Proof sketch

Linearization keeps each variable at degree one; a following quantifier or connective at most doubles the degree in the remaining variables, so degrees stay bounded by $2$ per variable between consecutive linearizations. Agreement on Boolean points preserves the value.

## Depends on

- [Arithmetization of quantified Boolean formulas](arithmetization-of-qbf.md)

## Proof depends on

- [IP = PSPACE (Shamir)](../ip-eq-pspace.md)

## Sources

- A. Shen, "IP = PSPACE: Simplified Proof", Journal of the ACM 39(4), 878–880, 1992.
- A. Shamir, "IP = PSPACE", Journal of the ACM 39(4), 869–877, 1992.
- C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic Methods for Interactive Proof Systems", Journal of the ACM 39(4), 859–868, 1992.
