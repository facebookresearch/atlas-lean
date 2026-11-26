# Dutta–Gesmundo–Ikenmeyer–Jindal–Lysikov: border Waring rank via product-plus-power

For a homogeneous polynomial $f$ of degree $d$ over $\mathbb{C}$, the following quantities agree up to a factor of $d$: (i) the border Waring rank $\underline{\mathrm{WR}}(f)$; (ii) the least $r$ such that $f$ lies in the border of polynomials of the form $c + \prod_{i=1}^{r} \ell_i$ with $\ell_i$ affine linear and $c$ a constant (Kumar's model). Moreover, every point in the orbit closure of the product-plus-power polynomial $x_1 \cdots x_r + y^r$ has a (non-border) algebraic branching program of size polynomial in $r$, and this orbit closure admits multiplicity obstructions constructed from the symmetries of the polynomial, against the power sum.

## Proof sketch

The direction from border Waring rank to Kumar's model is Kumar's limit construction. The converse expands $\prod_i (1 + \varepsilon\ell_i)$ around $\varepsilon = 0$ and extracts the homogeneous component of degree $d$ as a border combination of $d$-th powers via Fischer-type identities. Debordering uses the explicit description of the boundary of the orbit, and the obstruction part generalizes the Ikenmeyer-Kandasamy method to this orbit closure.

## Depends on

- [Orbit closures and border complexity of polynomials](orbit-closure-border.md)
- [Representation-theoretic occurrence and multiplicity obstructions](occurrence-obstruction.md)

## Proof depends on

- [Kumar: every homogeneous polynomial lies in the border of top-fan-in d+1 depth-three circuits](../depth-reduction-and-chasms/kumar-border-depth3.md)

## Sources

- P. Dutta, F. Gesmundo, C. Ikenmeyer, G. Jindal, V. Lysikov, "Geometric complexity theory for product-plus-power", arXiv:2211.07055 (2022), ECCC TR22-157.
- M. Kumar, "On the power of border of depth-3 arithmetic circuits", ACM Transactions on Computation Theory 12 (2020), arXiv:1804.03303.
