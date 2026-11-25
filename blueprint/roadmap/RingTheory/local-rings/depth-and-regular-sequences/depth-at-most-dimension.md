# The depth of a nonzero finitely generated module over a Noetherian local ring is at most its dimension

Let $(R, \mathfrak m)$ be a commutative Noetherian local ring and $M$ a nonzero finitely generated $R$-module. Then $\operatorname{depth} M \le \dim M$. Here $\operatorname{depth} M$ is the supremum of the lengths of the $M$-regular sequences in $\mathfrak m$, and $\dim M$ is the Krull dimension of $M$, that is, the Krull dimension of $R/\operatorname{ann} M$.

## Proof sketch

It suffices to show that $d \le \dim M$ for every $M$-regular sequence $x_1, \dots, x_d$ in $\mathfrak m$ and then to take the supremum; this does not assume that the depth is finite. Since $M$ is finitely generated, $\operatorname{Supp} M = V(\operatorname{ann} M)$, so $\dim M$ is the Krull dimension of $\operatorname{Supp} M$. Induct on $d$, the case $d = 0$ being trivial. Regularity makes the final quotient $M/(x_1, \dots, x_d)M$ nonzero, so $M' = M/x_1 M$ is a nonzero finitely generated module on which $x_2, \dots, x_d$ is a regular sequence, and $d - 1 \le \dim M'$ by induction. The zero divisors on $M$ are the union of its associated primes, so $x_1$, a nonzero divisor on $M$, lies in no associated prime of $M$, and hence in no minimal prime of $\operatorname{Supp} M$, since these are associated. As $\operatorname{Supp} M' = \operatorname{Supp} M \cap V(x_1)$, every chain of primes in $\operatorname{Supp} M'$ begins at a prime containing $x_1$, which contains a minimal prime of $\operatorname{Supp} M$ not containing $x_1$; prepending that prime gives a longer chain in $\operatorname{Supp} M$. Thus $\dim M' \le \dim M - 1$, so $d \le \dim M$; if $\dim M$ is infinite there is nothing to prove.

## Expansion

For the nonzero finitely generated module $M$ above, a good expansion bounds the length of every finite $M$-regular sequence $x_1, \dots, x_d$ in $\mathfrak m$ by the dimension of the support of $M$: each $x_i$ lowers the dimension of the support of the successive quotient $M/(x_1, \dots, x_{i-1})M$ by at least one, and the final quotient $M/(x_1, \dots, x_d)M$ is nonzero. It identifies the dimension of the support of $M$ with the Krull dimension of $R/\operatorname{ann} M$, using $\operatorname{Supp} M = V(\operatorname{ann} M)$, and then takes the supremum over all such sequences, which for this nonzero $M$ is its depth. A good expansion also links each prerequisite of its statement and proof: the fact that the minimal primes of the support are associated primes; the depth of a module; local rings; Noetherian rings.

## Depends on

- [Finitely generated module](../../modules/finitely-generated-module.md)
- [Krull dimension of a commutative semiring](../krull-dimension/krull-dimension.md)

## Proof depends on

- [Regular sequence on a module](../regular-sequence.md)
- [Support of a module](../../modules/module-support.md)
- [Support of the quotient M/IM of a finitely generated module](../../modules/support-quotient-by-ideal-times-module.md)
- [The zero divisors on a module over a Noetherian ring are the elements of its associated primes](../../noetherian-and-artinian-rings/associated-primes-of-modules/zero-divisors-associated-primes.md)

## Sources

- The Stacks Project, Section 10.72 (Tag 00LE), Lemma 10.72.3 (Tag 00LK).
- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer, 1995.
