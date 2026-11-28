# Quasi-identities of Hilbert lattices are undecidable

No algorithm decides which implications between equations of the form $P_1 \lor \cdots \lor P_k = 1$ and orthogonality relations $P \perp Q$ force a Hilbert space to be zero. So the quasi-identities of the lattices of closed subspaces of complex Hilbert spaces, in the signature $(\lor, \perp, 0, 1)$, are undecidable.

**Hilbert lattices.** For a complex Hilbert space $\mathcal{H}$, let $\mathrm{Cl}(\mathcal{H})$ be the lattice of closed subspaces of $\mathcal{H}$, equivalently of [orthogonal projections](../gleason-s-theorem/is-orth-proj.md) on $\mathcal{H}$. Here $P \lor Q$ is the closed span of $P \cup Q$, $P \perp Q$ means that $P$ and $Q$ are orthogonal, $0$ is the zero subspace and $1 = \mathcal{H}$.

**Theorem (Fritz).** There is no algorithm that decides whether a sentence of the form

$$
\forall P_1, \dots, P_n\ \bigl[(E_1 \wedge E_2 \wedge \cdots \wedge E_k) \Rightarrow (0 = 1)\bigr]
$$

holds in $\mathrm{Cl}(\mathcal{H})$ for every complex Hilbert space $\mathcal{H}$, where the variables range over $\mathrm{Cl}(\mathcal{H})$ and each $E_i$ is either an equation $P_{i_1} \lor \cdots \lor P_{i_m} = 1$ or an orthogonality relation $P_{i_1} \perp P_{i_2}$ between two variables.

Equivalently, no algorithm decides whether finitely many such conditions can be satisfied simultaneously by closed subspaces of some nonzero Hilbert space, a quantum analogue of Boolean satisfiability. The source shows that a satisfiable instance can always be satisfied in an infinite-dimensional separable Hilbert space. For example, three pairwise orthogonal subspaces of which any two span $\mathcal{H}$ exist only in the zero space, so that sentence holds.

## Depends on

- [Orthogonal projection](../gleason-s-theorem/is-orth-proj.md)
- [Complete lattice](../../../Order/lattices-boolean-algebras/complete-lattice.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Existence of a perfect commuting-operator strategy for a linear system game is undecidable](../tsirelson-problem-and-connes-embedding/perfect-commuting-operator-play-is-undecidable.md)

## Expansion

The proof starts from a result Slofstra derived in proving that perfect commuting-operator play of linear system games is undecidable: given a linear system $Mx = b$ over $\mathbb{Z}_2$, it is undecidable whether $J = 1$ in its solution group, equivalently whether the system has a quantum solution by self-adjoint unitaries on a nonzero Hilbert space, since a quantum solution exists exactly when $J \neq 1$. A quantum solution is a family of projective measurements whose outcomes, read as an assignment to the variables, satisfy every equation, with measurements for variables of a common equation commuting. Through the hypergraph approach to contextuality (Lemma 10 of the source), such a family is a quantum representation of a hypergraph with two kinds of vertices: a vertex $v_i^\alpha$ for each variable $i$ and value $\alpha \in \{\pm 1\}$, and a vertex $w_r^\beta$ for each equation $r$ and each assignment $\beta$ of values to its variables with the parity the equation requires. Its hyperedges are the pairs $\{v_i^{-1}, v_i^{+1}\}$, the sets $\{w_r^\beta\}_\beta$ for each equation $r$, and the sets $\{v_i^\alpha\} \cup \{w_r^\beta : \beta(i) = -\alpha\}$ for each equation $r$, variable $i$ in it and value $\alpha$, which tie the two kinds together. A quantum representation assigns a closed subspace to each vertex so that the subspaces of each hyperedge are pairwise orthogonal and jointly span $\mathcal{H}$. These are conditions of the two allowed forms. Hence the system has a quantum solution exactly when the corresponding antecedent is satisfiable in some nonzero $\mathcal{H}$. The source first proves the inverse sandwich conjecture (Corollary 11) and then derives the statement above from it.

## Sources

- T. Fritz, "Quantum logic is undecidable", *Archive for Mathematical Logic* 60(3–4):329–341, 2021, doi:[10.1007/s00153-020-00749-0](https://doi.org/10.1007/s00153-020-00749-0). Numbering of the version read, arXiv:1607.05870v5: Theorem 1, the two remarks and Example 4 that follow it, Theorem 6 (Slofstra's undecidability of $J = 1$), Lemma 10, Corollary 11 (inverse sandwich conjecture), Corollary 13, Theorem 14 and Lemma 15.
