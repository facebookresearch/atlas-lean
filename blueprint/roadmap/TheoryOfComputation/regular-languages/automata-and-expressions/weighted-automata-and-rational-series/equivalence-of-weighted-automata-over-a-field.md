# Equivalence of weighted automata over a field is decidable

Let $S$ be a computable field, or more generally a skew field. Given two [linear representations](linear-representations-of-recognizable-series.md)
of dimensions $n_1$ and $n_2$ over $S$, one can decide whether they define the same series, in time $O(|\Sigma| (n_1 + n_2)^3)$ counting field
operations as one step (Schützenberger). The difference of the two series has a linear representation of dimension $n_1 + n_2$, and a
representation $(\lambda, \mu, \gamma)$ defines the zero series exactly when $x \gamma = 0$ for a basis $x$ of the space spanned by the vectors
$\lambda \mu(w)$, which is reached by words of length at most the dimension. More generally, zeroness is decidable over computable semirings in which
these spans are always finitely generated semimodules, and equivalence over such rings.

## Depends on

- [Linear representations of recognizable series](linear-representations-of-recognizable-series.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Lemma 8.1, Corollary 8.2, Example 8.2, Theorem 8.3, Example 8.3, Corollary 8.4 and Remark 8.5.
