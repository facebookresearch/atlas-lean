# Conjugacy of multidimensional subshifts of finite type is Σ⁰₁-complete and factorization is Σ⁰₃-complete

For subshifts of finite type on $\mathbb Z^d$ with $d \ge 2$, deciding whether a given one is conjugate to a fixed one is $\Sigma^0_1$-complete, and deciding whether one factors onto another is $\Sigma^0_3$-complete in the arithmetical hierarchy.

**Theorem.** Let $d \ge 2$ and consider [subshifts of finite type](../aperiodic-domino-problem/subshifts-and-the-aperiodic-domino-problem.md) (SFTs) of $\Sigma^{\mathbb Z^d}$, given by finite sets of forbidden patterns. An SFT $X$ *factors onto* an SFT $Y$ if there are a finite window $V \subseteq \mathbb Z^d$ and a local map $f : \Sigma_X^V \to \Sigma_Y$ whose global map $F$, given by $F(x)_z = f(x|_{z+V})$, satisfies $F(X) = Y$; $X$ and $Y$ are *conjugate* if such an $F$ is invertible with inverse again given by a local map. Then:

1. for every fixed SFT $X$, the set of SFTs $Y$ conjugate to $X$ is $\Sigma^0_1$-complete (Theorem 0.1 of the source); and deciding, given $X$ and $Y$, whether they are conjugate is in $\Sigma^0_1$ (Theorem 2.1);
2. deciding, given two SFTs $X$ and $Y$, whether $X$ factors onto $Y$ is $\Sigma^0_3$-complete (Theorem 0.2).

Already for fixed simple targets factorization is hard: whether a given SFT factors onto the SFT consisting of one uniform configuration is $\Pi^0_1$-complete, and onto the empty SFT $\Sigma^0_1$-complete (Theorems 3.1 and 3.2).

## Depends on

- [Subshifts of finite type, sofic and effective subshifts](../aperiodic-domino-problem/subshifts-and-the-aperiodic-domino-problem.md)
- [Arithmetical class $\Sigma_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)
- [The cofiniteness index set is Σ⁰₃-complete](../../../degrees-and-hierarchies/arithmetical-hierarchy/cofiniteness-index-set-is-sigma03-complete.md)

## Expansion

*Conjugacy.* Membership in $\Sigma^0_1$: $X$ and $Y$ are conjugate iff there exist local maps $F$ and $G$ and a size $k$ such that, on every admissible block of size $k$, $F \circ G$ and $G \circ F$ act as the identity at the center, modified so as to detect forbidden patterns; by compactness this finite check is equivalent to conjugacy. Hardness: for a Turing machine $M$, Robinson's SFT $R_M$ is empty iff $M$ halts; let $Y_M$ be the disjoint union of $X$ and $R_M \times F$, where $F$ is the full shift on one more symbol than $X$. If $M$ halts, $Y_M = X$; otherwise $Y_M$ has larger entropy than $X$, and entropy is a conjugacy invariant. In dimension $d > 2$ the two-dimensional construction is extended by making symbols constant along the extra directions.

*Factorization.* The existence of a factor map is a $\Sigma^0_3$ statement, combining the $\Pi^0_2$ condition $Y \subseteq F(X)$ and the $\Sigma^0_1$ condition $F(X) \subseteq Y$ (Lemmas 3.4 and 3.5); hardness reduces the $\Sigma^0_3$-complete set of Turing machines that run forever on only finitely many inputs, using SFTs with a rigid "$T$-structure" that forces factor maps to respect the embedded computations (Definition 3.6, Lemma 3.7, Theorem 3.8).

## Sources

- Emmanuel Jeandel and Pascal Vanier, "Hardness of Conjugacy, Embedding and Factorization of multidimensional Subshifts of Finite Type", in *30th International Symposium on Theoretical Aspects of Computer Science (STACS 2013)*, Leibniz International Proceedings in Informatics 20, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2013, pp. 490–501, doi:[10.4230/LIPIcs.STACS.2013.490](https://doi.org/10.4230/LIPIcs.STACS.2013.490); read as arXiv:1204.4988v1, whose numbering is used here: Section 1 (SFTs, factorization and conjugacy), Theorems 0.1, 0.2, 2.1 and 2.2 with their proofs, Theorems 3.1 and 3.2, Lemmas 3.4 and 3.5, Definition 3.6, Lemma 3.7 and Theorem 3.8.
