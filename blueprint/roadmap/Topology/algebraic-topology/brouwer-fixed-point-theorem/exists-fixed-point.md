# Brouwer's fixed-point theorem for the standard simplex

Every continuous map $f$ of the standard simplex
$\Delta^n = \{x \in \mathbb{R}^{n+1} : x_i \ge 0,\ \sum_i x_i = 1\}$ to itself has a fixed point.

Proof: the closed sets $F_i = \{x : f(x)_i \le x_i\}$ satisfy the KKM condition
([the Brouwer sets satisfy the KKM covering condition](exists-pos-weights-le.md)), so by the
Knaster–Kuratowski–Mazurkiewicz lemma they share a point $x$; there $f(x)_i \le x_i$ for every $i$ and both sides
sum to $1$, so $f(x) = x$. This is the argument of B. Knaster, C. Kuratowski and S. Mazurkiewicz, "Ein Beweis des
Fixpunktsatzes für n-dimensionale Simplexe", Fundamenta Mathematicae 14 (1929), 132–137. The statement is Brouwer's
theorem restricted to the simplex; it is the form used by Nash-type existence proofs once strategy spaces are
simplices.

## Informally uses

- [Knaster–Kuratowski–Mazurkiewicz lemma](../../../Geometry/convex-geometry/kkm-lemma.md): applied to the closed sets $F_i = \{x : f(x)_i \leq x_i\}$, whose common point is the fixed point.
- [The Brouwer sets satisfy the KKM covering condition](exists-pos-weights-le.md): the covering hypothesis of the KKM lemma for these sets.
