# Learning size-s circuits from a dense property of functions with large circuit complexity

Fix $n, \ell, s, e, g, h$. There is an explicit bound $B(n,\ell,e,g,s)$, polynomial in $s$, $n$ and $2^{e+g}$, such that every function of the Nisan-Wigderson generator on $\mathrm{Amp}(f)$ has De Morgan circuit complexity at most $B$ whenever $f$ has complexity at most $s$. Let $\mathcal{D}$ be a set of Boolean functions on $\ell$ bits with $|\mathcal{D}| \ge 2^{2^\ell + \ell + 1 - g}$, each of De Morgan circuit complexity greater than $B$. Then the CIKK learner whose test accepts exactly the truth tables of $\mathcal{D}$ learns all functions on $n$ bits of De Morgan circuit complexity at most $s$, with error $2^{-e}$ and confidence $1 - 2^{-h}$.

## Proof sketch

Each generator output, viewed as a truth table on $\ell$ bits, is computed by a circuit built from a circuit for $f$ and the design's selector circuits, of size at most $B$. Every function in $\mathcal{D}$ has larger complexity, so the test rejects all generator outputs, and the density hypothesis matches. Apply the learner from a dense test.

## Depends on

- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)
- [Truth table](../natural-proofs-barrier/truth-table.md)

## Proof depends on

- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Alexander A. Razborov and Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences, 1997.
