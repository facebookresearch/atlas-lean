# Buchberger's criterion

Let $k$ be a field and fix a monomial order on the monomials of the polynomial ring
$k[x_i : i \in \sigma]$. Let $G$ be a set of nonzero polynomials. If for all $g, h \in G$ the
S-polynomial $S(g, h)$ can be written as $\sum_{b \in G} q_b\, b$ with no summand $q_b\, b$ of
leading monomial above that of $S(g, h)$, then $G$ is a Gröbner basis of the ideal it generates.

Such a representation is what a division of $S(g, h)$ by $G$ with zero remainder provides, so the
criterion reduces the infinitely many checks in the definition of a Gröbner basis to finitely many
divisions when $G$ is finite. Buchberger's algorithm adds the nonzero remainders of S-polynomials
to $G$ until the criterion holds; it terminates by the ascending chain condition on monomial ideals.
The converse, that every S-polynomial of a Gröbner basis has remainder zero, is [S-polynomials of a
Gröbner basis reduce to zero](s-polynomial-remainder-eq-zero.md).

As in Hassett's proof, write an element $f = \sum_b q_b\, b$ of the ideal with the largest leading
monomial $\delta$ of the summands as small as possible. If the $x^\delta$ terms do not cancel,
$\delta$ is the leading monomial of $f$ and is divisible by the leading monomial of some $b$. If
they cancel, the identity

$$c\, x^{\alpha} g_i = \frac{c\, \mathrm{lc}(g_i)}{\mathrm{lc}(g_j)}\, x^{\delta - \deg g_j} g_j + \frac{c}{\mathrm{lc}(g_j)}\, x^{\delta - \gamma} S(g_i, g_j),$$

with $\gamma$ the least common multiple of the leading monomials, moves the top term of one summand
onto another and puts the rest below $\delta$; induction on $\delta$ and on the number of summands
reaching it concludes. Here
$S(f, g) = \mathrm{lc}(g)\, x^{\gamma - \deg f} f - \mathrm{lc}(f)\, x^{\gamma - \deg g} g$, which
differs from the textbook S-polynomial by the nonzero factor $\mathrm{lc}(f)\, \mathrm{lc}(g)$.

## Sources

- D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Ch. 2 §6, Theorem 6 (Buchberger's criterion, remainder-zero form), and §7 (Buchberger's algorithm, section only).
- B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 5, Theorem 5.2 and Corollary 5.3 (https://www.math.brown.edu/bhassett/teaching/465spring02/). Its proof of `⇐` uses exactly the standard representations assumed here and the same double minimality.
- B. Buchberger, *Ein Algorithmus zum Auffinden der Basiselemente des Restklassenringes nach einem nulldimensionalen Polynomideal*, PhD thesis, Innsbruck, 1965.
