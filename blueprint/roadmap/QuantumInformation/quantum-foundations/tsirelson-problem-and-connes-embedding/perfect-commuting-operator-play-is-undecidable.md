# Existence of a perfect commuting-operator strategy for a linear system game is undecidable

No algorithm decides, given a linear system over $\mathbb{Z}_2$, whether the associated nonlocal game can be won with probability 1 by a commuting-operator strategy.

**Theorem (Slofstra).** It is undecidable to determine whether a binary [linear system game](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md) has a perfect [commuting-operator strategy](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md). The input is a linear system $Ax = b$ over $\mathbb{Z}_2$; a strategy is perfect when it wins with probability 1.

The game of $Ax = b$ has a perfect commuting-operator strategy exactly when $J \neq 1$ in the *solution group* $\Gamma$ of the system. $\Gamma$ is the finitely presented group with generators $g_1, \dots, g_n$ and $J$, subject to these relations: $J$ is central, $g_i^2 = J^2 = 1$, $g_i g_j = g_j g_i$ when $x_i$ and $x_j$ occur in a common equation, and $\prod_{i : A_{\ell i} = 1} g_i = J^{b_\ell}$ for each equation $\ell$ (Cleve, Liu and Slofstra; Theorem 2.3 of the source). For comparison, the game has a perfect finite-dimensional strategy exactly when $\Gamma$ has a finite-dimensional representation $\pi$ with $\pi(J) \neq 1$ (Cleve and Mittal).

## Depends on

- [Linear constraint system games and operator solutions](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md)
- [Commuting-operator strategies and value](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The proof rests on the source's embedding theorem (Theorem 3.1): every finitely presented group $G$ embeds in the solution group $\Gamma$ of some linear system, constructively, in such a way that a given central element $J_0$ of order dividing 2 in $G$ is sent to $J$. By the characterization above, deciding perfect commuting-operator play is equivalent to deciding, for a finite presentation of a group $G$ and a word $J_0$ that is central with $J_0^2 = 1$, whether $J_0 = 1$ in $G$. The word problem for finitely presented groups reduces to this question. Given $K = \langle S : R\rangle$ and a word $w$, a construction the source attributes to Rabin gives a finitely presented group that contains $K$ when $w \neq 1$ and is trivial when $w = 1$. Applied to $K \times \mathbb{Z}$, it gives a group $H_w$ with an element $z$ of infinite order when $w \neq 1$ and $z = 1$ when $w = 1$. Adding generators $x$ and $J$ with $J^2 = [x, J] = 1$, $J$ central and $[x, z] = J$ gives a group $G_w$. When $w \neq 1$, $G_w$ is an HNN extension of $H_w \times \mathbb{Z}_2$ and $J \neq 1$; when $w = 1$, $J = [x, 1] = 1$. The word problem for finitely presented groups is undecidable (Novikov; Boone).

## Sources

- W. Slofstra, "Tsirelson's problem and an embedding theorem for groups arising from non-local games", *Journal of the American Mathematical Society* 33(1):1–56, 2020, doi:[10.1090/jams/929](https://doi.org/10.1090/jams/929). Numbering of the version read, arXiv:1606.03140v3: Corollary 3.3 and its proof, Theorem 3.1 (embedding theorem) and Theorem 2.3 (characterization of perfect strategies, quoted from Cleve and Mittal and from Cleve, Liu and Slofstra).
