# Saxena's duality trick for powers of sums of products

Let $\mathbb{F}$ have characteristic $0$ or larger than $ad$. For polynomials $g_1, \dots, g_a$ of degree at most $t$ in $x$, the power $(g_1 + \cdots + g_a)^d$ can be written as

$$
(g_1 + \cdots + g_a)^d = \sum_{i=1}^{m} \prod_{j=1}^{a} h_{i,j}\bigl(g_j\bigr), \qquad m = O\bigl(a d\bigr),
$$

where each $h_{i,j}$ is a univariate polynomial of degree at most $d$. In particular, a power of a linear form is a sum of $O(nd)$ products of univariate polynomials in the individual variables.

## Proof sketch

Write $(\sum_j z_j)^d$ as the coefficient of $y^d$ in $d! \prod_j e^{y z_j}$ truncated at degree $d$, and recover that coefficient by interpolation from $ad + 1$ distinct values of $y$. Each evaluation is a product over $j$ of truncated exponentials of $y z_j$, which are univariate polynomials in $z_j$; substituting $z_j = g_j$ gives the identity.

## Proof depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)

## Sources

- N. Saxena, "Diagonal circuit identity testing and lower bounds", ICALP (2008).
- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Arithmetic circuits: a chasm at depth three", FOCS (2013); SIAM Journal on Computing 45 (2016) 1064-1079.
