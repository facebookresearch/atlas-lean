# Isomorphism of automatic trees of height at most n is Π⁰₂ₙ₋₃-complete

For automatic trees, each additional level of height raises the complexity of isomorphism by two quantifier alternations, and for trees of arbitrary finite height it is as hard as true arithmetic.

**Theorem.** A *tree* is a structure $(V; \le)$ where $\le$ is a partial order with a least element and the set of ancestors of every node is a finite linear order; its height is the supremum of the levels $|\{y : y < x\}|$ of its nodes. Let $\mathcal T_n$ be the class of [automatic](automatic-structure.md) trees of height at most $n$.

1. For every $n \ge 2$, the isomorphism problem for $\mathcal T_n$ is complete for the class [$\Pi^0_{2n-3}$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md) of the arithmetical hierarchy.
2. The isomorphism problem for automatic trees of finite height is recursively equivalent to the first-order theory of $(\mathbb N; +, \times)$ (true arithmetic).

For $n = 1$ the problem is decidable (Proposition 7 of the source). For recursive trees, given by Turing machines, the isomorphism problem for trees of height at most $n$ is $\Pi^0_{2n}$-complete (Theorem 19), three levels higher in the arithmetical hierarchy at every height $n \ge 2$.

## Depends on

- [Automatic structure](automatic-structure.md)
- [Arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Partially ordered set](../../../../Order/ordered-sets/partial-order.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Isomorphism of automatic equivalence structures is Π⁰₁-complete](isomorphism-of-automatic-equivalence-structures.md)

## Expansion

*Upper bound.* Two trees of height $n$ are isomorphic iff, for the roots' children, every isomorphism type of subtree occurs the same number of times in both; unfolding this level by level, and using that counting quantifiers over automatic structures are decidable, expresses isomorphism of trees in $\mathcal T_n$ by a $\Pi^0_{2n-3}$ formula (Proposition 7).

*Lower bound.* The case $n = 2$ is the equivalence-structure reduction. For larger $n$ every $\Pi^0_{2n-3}$ predicate $P$ is brought into a normal form with monotonicity properties (Lemma 8), and from polynomials obtained by the solution of Hilbert's tenth problem one builds a single automatic forest $F^n$ of height $n$ containing trees $T^n_c$ and $U^n_\omega$ with $T^n_c \cong U^n_\omega$ iff $P(c)$ holds (Proposition 14). For trees of finite height, the height is computable from a presentation and the reductions are uniform in $n$, which gives part 2.

## Sources

- D. Kuske, J. Liu and M. Lohrey, "The Isomorphism Problem on Classes of Automatic Structures", in *Proceedings of the 25th Annual IEEE Symposium on Logic in Computer Science (LICS 2010)*, IEEE Computer Society, 2010, pp. 160–169, doi:[10.1109/LICS.2010.10](https://doi.org/10.1109/LICS.2010.10); read as arXiv:1001.2086v1, whose numbering is used here: Section 4 (trees, Corollary 6, Proposition 7, Lemma 8, Proposition 14, Theorem 18 with its proof) and Theorem 19.
