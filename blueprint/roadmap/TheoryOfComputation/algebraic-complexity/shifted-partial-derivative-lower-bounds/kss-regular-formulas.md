# Kayal–Saha–Saptharishi: superpolynomial lower bounds for regular formulas

Call an arithmetic formula **regular** if it consists of alternating layers of addition and multiplication gates in which all multiplication gates in the same layer have the same fan-in. There is an explicit family in $\mathrm{VNP}$ (a Nisan-Wigderson design polynomial on $N$ variables of degree $d = N^{\Theta(1)}$) that requires regular formulas of size $N^{\Omega(\log N)}$. Since the iterated matrix multiplication polynomial has regular formulas of size $N^{O(\log N)}$, the bound shows the limits of regular formulas.

## Proof sketch

A regular formula of small size can be depth-reduced into a homogeneous $\Sigma\Pi\Sigma\Pi^{[t]}$ circuit whose number of product gates is small relative to the bottom fan-in, because regularity bounds the formal degree. The shifted partials of the design polynomial are near-maximal, contradicting the product upper bound for that depth-four form.

## Depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [Shifted partials of a product of low-degree polynomials](spd-product-upper-bound.md)

## Proof depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [Shifted partials of a product of low-degree polynomials](spd-product-upper-bound.md)

## Sources

- N. Kayal, C. Saha, R. Saptharishi, "A super-polynomial lower bound for regular arithmetic formulas", STOC (2014), ECCC TR13-091.
