# Disjointness of infinitary rational relations is Π¹₁-complete

Deciding whether two infinitary rational relations, given by Büchi transducers, are disjoint is $\Pi^1_1$-complete.

**Theorem.** The set of pairs $(z, z')$ of (codes of) Büchi transducers such that $R(\mathcal{T}_z) \cap R(\mathcal{T}_{z'}) = \emptyset$,
in the sense of [infinitary rational relations](infinitary-rational-relations-and-omega-rational.md), is [$\Pi^1_1$-complete](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md).

Equivalently, non-emptiness of the intersection of two infinitary rational relations is $\Sigma^1_1$-complete. For relations
between finite words, disjointness of rational relations is undecidable; the source also
recalls that universality, equivalence and inclusion of infinitary rational relations are $\Pi^1_2$-complete.

## Depends on

- [Infinitary rational relations and ω-rational functions](infinitary-rational-relations-and-omega-rational.md)
- [Analytical hierarchy](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The infinite PCP in a regular ω-language is Σ¹₁-complete](../../../../undecidable-problems/post-correspondence-problem/infinite-pcp-in-a-regular-omega-language-is.md)

## Expansion

Non-emptiness of $R(\mathcal{T}_z) \cap R(\mathcal{T}_{z'})$ is $\Sigma^1_1$, since a Büchi Turing machine accepting the
intersection can be computed from $z, z'$. For hardness, given an instance $((x_i), (y_i), \mathcal{A})$ of the infinite PCP in
a regular ω-language, build transducers relating each index sequence $i_1 i_2 \cdots \in L(\mathcal{A})$ to
$x_{i_1} x_{i_2} \cdots$ and to $y_{i_1} y_{i_2} \cdots$ respectively; their relations intersect exactly when the instance has
a solution.

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Theorem 4.2.
