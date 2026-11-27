# Perfect play of linear system games in the quantum-approximate and finite-dimensional models is undecidable

It is undecidable whether a linear system game has a perfect strategy in the closure $C_{qa}$ of the finite-dimensional quantum correlations, and also whether it has a perfect strategy in the finite-dimensional set $C_q$ itself.

A [linear system game](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md) is built from a binary linear system $Ax = b$ over $\mathbb{Z}_2$. For a set $C_t$ of [quantum correlations](quantum-correlation-sets-q-qs-qa-qc.md), $t \in \{q, qa, qc\}$, the game has a *perfect strategy in $C_t$* if some correlation in $C_t$ wins it with probability $1$.

**Theorem (Slofstra).**

1. There is a recursive family of linear system games such that it is undecidable to determine whether a game in the family has a perfect strategy in $C_{qa}$, and every game in the family has a perfect strategy in $C_{qc}$ if and only if it has one in $C_{qa}$ (Theorem 1.2 of the source).
2. It is undecidable to determine whether a linear system game has a perfect strategy in $C_q$ (Corollary 1.4).

Here the input is the linear system; in clause 1 it is drawn from a fixed computable family. Since a game has a perfect strategy in $C_{qa}$ exactly when its finite-dimensional quantum value is $1$, clause 1 shows that deciding whether the quantum value of a game is $1$ is hard for $\mathrm{coRE}$; the exact complexity of that problem was later shown to be $\Pi^0_2$-complete ([exact quantum value one is Π⁰₂-complete](exact-quantum-value-one-is-pi02-complete.md)).

## Depends on

- [Linear constraint system games and operator solutions](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md)
- [Quantum correlation sets C_q, C_qs, C_qa and C_qc](quantum-correlation-sets-q-qs-qa-qc.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A linear system game has a perfect strategy in a given model exactly when a distinguished central element $J$ is nontrivial in suitable approximate or finite-dimensional representations of its solution group. The source proves a restricted embedding theorem: every group in a class of finitely presented "linear-plus-conjugacy" groups embeds in the solution group of a linear system game in a way that preserves the relevant approximate (hyperlinear) or finite-dimensional representations. Applied to Kharlampovich's finitely presented solvable group with undecidable word problem, this reduces the word problem of that group to the existence of perfect $C_{qa}$ strategies for a computable family of games, which yields clause 1. Applied to finitely presented residually finite groups of Kharlampovich, Myasnikov and Sapir, whose word problems can be as hard as any computable function, it yields a family of games for which membership in the set of games with a perfect strategy in $C_q$ needs running time beyond any computable bound (Theorem 1.3), and hence clause 2. None of these group-theoretic ingredients has a page.

## Sources

- W. Slofstra, "The set of quantum correlations is not closed", Forum of Mathematics, Pi 7 (2019), e1, https://doi.org/10.1017/fmp.2018.3; read in arXiv:1703.08618v2 (Theorems 1.2 and 1.3 and Corollary 1.4 of arXiv:1703.08618v2).
- H. Mousavi, S. S. Nezhadi and H. Yuen, "Nonlocal games, compression theorems, and the arithmetical hierarchy", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022), 1–11, https://doi.org/10.1145/3519935.3519949; read in arXiv:2110.04651v2 (Section 1 of arXiv:2110.04651v2, which records Slofstra's result as $\mathrm{coRE}$-hardness of the exact quantum value problem).
