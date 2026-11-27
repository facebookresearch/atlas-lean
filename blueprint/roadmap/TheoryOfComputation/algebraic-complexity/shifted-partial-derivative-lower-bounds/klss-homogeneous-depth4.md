# Kayal–Limaye–Saha–Srinivasan: exponential lower bounds for homogeneous depth-four formulas

Over any field of characteristic $0$, there is an explicit family $\{P_d\}$ in $\mathrm{VNP}$ (the Nisan-Wigderson design polynomial $\mathrm{NW}_r$ over $\mathbb{F}_{d^2}$) with $P_d$ of degree $d$ in $N = d^3$ variables (and more generally in any $N \ge d^{2+\varepsilon}$ variables for fixed $\varepsilon > 0$) such that every homogeneous $\Sigma\Pi\Sigma\Pi$ formula computing $P_d$, with no restriction on bottom fan-in, has size $2^{\Omega(\sqrt{d}\log d)}$ (and $N^{\Omega(\sqrt{d})}$ for general $N \ge d^{2+\varepsilon}$). Over any field (of arbitrary characteristic), Kumar and Saraf proved a superpolynomial homogeneous depth-four lower bound of $n^{\Omega(\sqrt{n})}$ (for degree $n$ in $N = n^{O(1)}$ variables) for an explicit family in $\mathrm{VP}$.

## Proof sketch

Handle large bottom fan-in by random restriction: setting each variable to zero independently with suitable probability kills every bottom monomial of high support with high probability while the design polynomial retains rich structure. On the restricted circuit all bottom monomials have small support, and projected shifted partials separate the restricted circuit from the restricted target.

## Depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [Homogeneous depth-four circuits with bounded bottom fan-in](../depth-reduction-and-chasms/homogeneous-depth-four.md)

## Proof depends on

- [Shifted partials of a product of low-degree polynomials](spd-product-upper-bound.md)

## Sources

- N. Kayal, N. Limaye, C. Saha, S. Srinivasan, "An exponential lower bound for homogeneous depth four arithmetic formulas", SIAM Journal on Computing 46 (2017); FOCS (2014).
- M. Kumar, S. Saraf, "On the power of homogeneous depth 4 arithmetic circuits", SIAM Journal on Computing 46 (2017); FOCS (2014).
