# Every regular local ring is Cohen-Macaulay

Every regular local ring is a Cohen-Macaulay local ring.

## Proof sketch

Let $d = \dim R$ and let $x_1, \dots, x_d$ be a regular system of parameters. Each quotient $R/(x_1, \dots, x_i)$ is a regular local ring of dimension $d - i$, hence an integral domain. For $i < d$ the image of $x_{i+1}$ is a minimal generator of its nonzero maximal ideal, so it is nonzero and therefore a nonzerodivisor. Since $R/(x_1, \dots, x_d)$ is the nonzero field $R/\mathfrak m$, the sequence $x_1, \dots, x_d$ is $R$-regular. By the ascending chain condition it extends to a maximal regular sequence in $\mathfrak m$, so $\operatorname{depth} R \ge d$. The bound of depth by dimension gives equality.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: Depth of a finitely generated module M over a Noetherian local ring; Noetherian rings; quotients of a regular local ring by an element of $\mathfrak m \setminus \mathfrak m^2$; Regular local ring.

## Depends on

- [Cohen–Macaulay local ring](../depth-and-regular-sequences/cohen-macaulay-local-ring.md)

## Proof depends on

- [Regular local rings are domains](regular-local-rings-are-domains/is-domain.md)
- [Regular sequence on a module](../regular-sequence.md)
- [The depth of a nonzero finitely generated module over a Noetherian local ring is at most its dimension](../depth-and-regular-sequences/depth-at-most-dimension.md)

## Sources

- Winfried Bruns and Jürgen Herzog, Cohen–Macaulay Rings, 2nd ed., Cambridge University Press, 1998.
