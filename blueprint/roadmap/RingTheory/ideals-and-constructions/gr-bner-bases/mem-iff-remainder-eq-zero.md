# Ideal membership by remainder zero

Let $k$ be a field and fix a monomial order on the monomials of the polynomial ring
$k[x_i : i \in \sigma]$. Let $G$ be a Gröbner basis of an ideal $I$, and write
$f = \sum_{b \in G} q_b\, b + r$, with finitely many nonzero $q_b$, where no monomial of $r$ is
divisible by the leading monomial of any $b \in G$, as the division algorithm produces. Then
$f \in I$ if and only if $r = 0$.

If $f \in I$ then $r \in I$; a nonzero $r$ would have its leading monomial divisible by that of some
element of $G$, which the shape of the remainder forbids. This is what makes Gröbner bases solve the
ideal membership problem: one division, in any order, decides it.

## Sources

- B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 3, Proposition 3.8 (https://www.math.brown.edu/bhassett/teaching/465spring02/).
- D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Ch. 2 §6 (section only).
