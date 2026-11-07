# Oesper's determinant formula for three-strand weaving knots

Let $k \ge 1$ be an integer,
let $F_i$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$), let
$C_j = \sum_{i=1}^{j} (-1)^{i+1} F_i$ for $j \ge 0$, and let $M$ be the $3 \times 3$ integer
matrix with rows $(2, -1, 0)$, $(0, 0, 1)$ and $(-1, 0, 2)$. Then the absolute value of the
determinant of the $2 \times 2$ matrix obtained from $M^k - I$ by deleting its first row and
first column equals $-(C_{2k-2} + 1) C_{2k} + C_{2k-1}^2$.

Here $M$ is the base-word matrix of the spiral knot $S(3, k, (1, -1))$, which is the
three-strand weaving knot $W(k, 3)$, and the left-hand side is the determinant of this knot:
the cofactor minors of $M^k - I$ agree up to sign, so taking the absolute value gives the
nonnegative knot determinant.

## Sources

- Seong Ju Kim, Ryan Stees, and Laura Taalman, "Sequences of Spiral Knot Determinants", Journal of Integer Sequences 19 (2016), Article 16.1.4, lines 409-412: https://cs.uwaterloo.ca/journals/JIS/VOL19/Stees/stees4.tex The formula is attributed to L. Oesper, "p-colorings of weaving knots" (preprint). Proves `Wanted` entry `oesper_weaving_three_determinant`.
