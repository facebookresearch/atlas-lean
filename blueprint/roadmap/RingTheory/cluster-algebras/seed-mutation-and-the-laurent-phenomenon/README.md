# Seed mutation and the Laurent phenomenon

A seed is a pair $(\mathbf{x}, B)$ of a cluster $\mathbf{x} = (x_1, \dots, x_n)$ of free generators of a field and a skew-symmetrizable integer matrix $B$. The mutation $\mu_k$ in direction $k$ replaces $B$ by the matrix $\mu_k(B)$ of formula (2.7.1) and replaces $x_k$ by $x_k'$ with $x_k x_k' = \prod_{b_{ik} > 0} x_i^{b_{ik}} + \prod_{b_{ik} < 0} x_i^{-b_{ik}}$; it is an involution. The cluster variables are all the elements obtained by iterating mutations (Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Definitions 2.7.4, 2.7.6, 3.1.3 and 3.1.9). The Laurent phenomenon says that every cluster variable is a Laurent polynomial with integer coefficients in the initial cluster, although each mutation divides by a polynomial (Theorem 3.3.1; Fomin and Zelevinsky, *Cluster algebras I*, J. Amer. Math. Soc. 15 (2002), Theorem 3.1, proved through the Caterpillar Lemma of Fomin and Zelevinsky, *The Laurent phenomenon*, Adv. in Appl. Math. 28 (2002), Theorem 2.1). Its arithmetic shadow is the integrality of the Somos-4 sequence $1, 1, 1, 1, 2, 3, 7, 23, 59, \dots$, obtained from a quiver whose mutations rotate it (Example 3.4.3).

Matrix mutation is an involution and preserves skew-symmetrizability (Exercise 2.7.7). The finite
types of rank two are treated in [Cluster algebras of rank
two](../cluster-algebras-of-rank-two/README.md).

- [Matrix mutation](matrix-mutation.md)
- [Skew-symmetrizable integer matrix](is-skew-symmetrizable.md)
- [Matrix mutation is an involution](matrix-mutation-matrix-mutation.md)
- [Matrix mutation preserves skew-symmetrizability](is-skew-symmetrizable-matrix-mutation.md)
- [Seed mutation without frozen variables](seed-mutation.md)
- [Iterated seed mutation](mutate-seq.md)
- [Cluster variables of a seed pattern](cluster-variables.md)
- [Initial cluster of the ambient field](initial-cluster.md)
- [Laurent polynomials in the initial cluster](laurent-subalgebra.md)
- [Rank-two Laurent phenomenon in any field](rank-two-seq-mem.md)
- [Laurent phenomenon (coefficient-free)](laurent-phenomenon.md)
- [Laurent phenomenon in rank two](rank-two-seq-mem-laurent-subalgebra.md)
- [Somos-4 sequence](somos4.md)
- [Positivity of the Somos-4 sequence](somos4-pos.md)
- [Somos-4 recurrence](somos4-add-four-mul.md)
- [First terms of the Somos-4 sequence](somos4-four-to-nine.md)
- [Integrality of the Somos-4 sequence](somos4-is-int.md)

## Related topics

- [Cluster algebras of rank two](../cluster-algebras-of-rank-two/README.md): explicit Laurent polynomials and periodicity for the rank-two exchange recurrences of types $A_2$, $B_2$, $G_2$.
- [Finite type criterion for cluster algebras](../finite-cluster-variables-iff.md): which exchange matrices give finitely many cluster variables.
