# Linearized arithmetization has low degree

Let $\varphi = Q_1 x_1 \cdots Q_n x_n\, \psi$ be a closed prenex quantified Boolean formula whose matrix $\psi$ has size $m$, and let $P_\psi$ be the arithmetization of $\psi$, of total degree at most $m$. Following Shen, first linearize every variable of the matrix and then, after each quantifier, linearize the variables still free: evaluate $Q_1 x_1\, L_{x_1}\, Q_2 x_2\, L_{x_1} L_{x_2} \cdots Q_n x_n\, L_{x_1} \cdots L_{x_n}\, P_\psi$, applying the operators from right to left. Every polynomial produced after the initial block $L_{x_1} \cdots L_{x_n}$ has degree at most $2$ in each variable (those inside that block have total degree at most $m$), and the value is $1$ if $\varphi$ is true and $0$ otherwise. Linearizing the matrix first is necessary: for $\exists y\, \forall x\, (y \wedge y \wedge y)$ the matrix arithmetizes to $y^3$, and applying $\forall x$ directly gives $y^6$. This degree bound is what makes the sum-check style interactive proof of $\mathrm{IP} = \mathrm{PSPACE}$ run with polynomially many rounds over a field of polynomial size.

## Proof sketch

After $L_{x_1} \cdots L_{x_i}$ the polynomial is multilinear in $x_1, \dots, x_i$, the only variables still free; the quantifier $Q_i x_i$ multiplies its two restrictions to $x_i \in \{0,1\}$ (or their complements), so each remaining variable has degree at most $2$, and a linearization lowers one variable to degree $1$ without raising the others. Every operator agrees with the plain arithmetization on Boolean points, which preserves the value.

## Depends on

- [Arithmetization of quantified Boolean formulas](arithmetization-of-qbf.md)

## Sources

- A. Shen, "IP = PSPACE: Simplified Proof", Journal of the ACM 39(4), 878–880, 1992.
- A. Shamir, "IP = PSPACE", Journal of the ACM 39(4), 869–877, 1992.
- C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic Methods for Interactive Proof Systems", Journal of the ACM 39(4), 859–868, 1992.
