# Gröbner bases

A Gröbner basis of an ideal $I$ of a polynomial ring over a field, for a monomial order, is a subset
of $I$, finite in practice, whose leading monomials generate the initial ideal of $I$. Division by a
Gröbner basis has a unique remainder, which decides ideal membership, and Buchberger's criterion,
that every S-polynomial reduces to zero, turns this into an algorithm. For the lexicographic order a
Gröbner basis contains Gröbner bases of all elimination ideals, which is how Gröbner bases eliminate
variables.

- [Gröbner basis](is-groebner-basis.md)
- [Ideal membership by remainder zero](mem-iff-remainder-eq-zero.md)
- [A Gröbner basis generates its ideal](span-eq.md)
- [S-polynomials of a Gröbner basis reduce to zero](s-polynomial-remainder-eq-zero.md)
- [Buchberger's criterion](is-groebner-basis-of-s-polynomial.md)
- [Lexicographic order and final segments of variables](lex-le-vanish.md)
- [Elimination Theorem](elimination.md)

## Related topics

- [Toric ideals and Markov bases](../toric-ideals-and-markov-bases/README.md): the reduced Gröbner basis of a toric ideal consists of binomials, and its moves form a Markov basis, which is how Diaconis and Sturmfels compute moves.
- [Hilbert's Nullstellensatz](../hilbert-s-nullstellensatz/README.md): Gröbner bases decide the membership questions that the Nullstellensatz reduces to, such as whether a system of polynomial equations has no common zero.
