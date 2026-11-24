# Rank-two Laurent phenomenon in any field

For positive integers `b, c` and elements
`x, y` of a field, every term of the rank-two exchange recurrence `rankTwoSeq b c x y` lies in
every subring containing `x`, `y` and their inverses, that is, in the image of `ℤ[x^{±1}, y^{±1}]`.
For the initial cluster of `ℚ(x, y)` this is the Laurent phenomenon in rank two (Fomin, Williams
and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Section 3.2
with Theorem 3.3.1; Fomin and Zelevinsky, *Cluster algebras I*, J. Amer. Math. Soc. 15 (2002),
Theorem 3.1). Here `x, y` are arbitrary and no term needs to be nonzero: with Lean's convention
`a / 0 = 0`, the terms after a vanishing one stay in the subring.
