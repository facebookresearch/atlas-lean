# For XOR games the entangled and commuting-operator values coincide and are attained

For every two-player XOR game $G$ (answers in $\{0,1\}$ and $V$ depending only on $a \oplus b$), $\omega^*(G) = \omega^{co}(G)$, the value is attained by a strategy of dimension $2^{\lceil |\mathcal{X}|/2 \rceil}$, and it equals the optimum of an explicit semidefinite program. In particular no XOR game separates $C_{qa}$ from $C_{qc}$; the separating games of the negative answer to Tsirelson's problem are necessarily not XOR games.

## Proof sketch

The bias of an XOR game strategy depends only on the correlation matrix $\langle \psi | A_x B_y | \psi \rangle$ of $\pm 1$ observables. Tsirelson's theorem identifies these matrices, for commuting and for tensor-product strategies alike, with Gram matrices of unit vectors; unit vectors in $\mathbb{R}^m$ are realized by Clifford-algebra observables of dimension $2^{\lceil m/2 \rceil}$.

## Depends on

- [Quantum correlation sets C_q, C_qs, C_qa and C_qc](quantum-correlation-sets-q-qs-qa-qc.md)
- [Two-player nonlocal games: classical and entangled values](../two-player-nonlocal-games-classical-and-entangled-values.md)

## Proof depends on

- [Classical and entangled values of the CHSH game](../classical-and-entangled-values-of-the-chsh-game.md)
- [Tsirelson's bound is attained](../tsirelson-bound-tight.md)

## Sources

- Boris S. Tsirelson, "Quantum generalizations of Bell's inequality", Letters in Mathematical Physics 4 (1980).
- Richard Cleve, Peter Hoyer, Benjamin Toner, John Watrous, "Consequences and limits of nonlocal strategies", CCC (2004); arXiv:quant-ph/0404076.
