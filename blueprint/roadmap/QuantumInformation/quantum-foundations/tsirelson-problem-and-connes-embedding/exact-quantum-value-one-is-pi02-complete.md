# Deciding whether the quantum value of a nonlocal game is 1 is Π⁰₂-complete

Deciding whether the finite-dimensional quantum value of a two-player nonlocal game equals $1$ is complete for the class $\Pi^0_2$ of the arithmetical hierarchy, so it is strictly harder than both the halting problem and its complement.

For a two-player one-round [nonlocal game](../two-player-nonlocal-games-classical-and-entangled-values.md) $G$, the *quantum value* is

$$
\omega_q(G) = \sup_{S} \omega(G, S),
$$

the supremum of the winning probability over finite-dimensional strategies $S$, which in finite dimension coincide with [tensor-product strategies](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md). The *exact $q$-value problem* asks, given $G$, whether $\omega_q(G) = 1$. The class $\Pi^0_2$ is defined on the page on the [arithmetical classes](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md).

**Theorem (Mousavi–Nezhadi–Yuen).** The problem of deciding whether $\omega_q(G) = 1$ for nonlocal games $G$ is complete for $\Pi^0_2$ (Theorem 1.1 of the source; membership in $\Pi^0_2$ is Lemma 6.8).

The value $\omega_q(G) = 1$ need not be attained by any finite-dimensional strategy. By comparison, the gapped problem of deciding whether $\omega_q(G) = 1$ or $\omega_q(G) \le 1/2$ is complete for $\Sigma^0_1$ (Ji, Natarajan, Vidick, Wright and Yuen), and the exact commuting-operator value problem, whether $\omega_{co}(G) = 1$, is complete for $\Pi^0_1$ (Slofstra). The source left open the complexity of the gapped commuting-operator problem; it was later shown to be $\mathrm{coRE}$-complete (Lin, see [the commuting-operator value problem](commuting-operator-value-gap-problem-is-core-complete.md)).

## Depends on

- [Two-player nonlocal games: classical and entangled values](../two-player-nonlocal-games-classical-and-entangled-values.md)
- [Entangled strategies and the entangled value of a game](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md)
- [The arithmetical class Pi_n](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Halting of a code on an input](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Approximating the entangled value of a nonlocal game is undecidable](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/entangled-value-is-uncomputable.md)

## Expansion

Membership: $\omega_q(G) = 1$ holds exactly when for every $\varepsilon > 0$ there is a finite-dimensional strategy winning with probability at least $1 - \varepsilon$, which the source writes as a $\Pi^0_2$ sentence (Lemma 6.8). Hardness: the centerpiece of the source is a *gapless* compression theorem for nonlocal games, which maps a sequence of games to a sequence of exponentially more succinct games, preserves the property of having value less than $1$, keeps the value close to $1$ when it is close to $1$, and raises the dimension needed for value $1$. Combining it with the gap-preserving compression theorem behind $\mathrm{MIP}^* = \mathrm{RE}$, the source maps every $\Pi^0_2$ sentence $\forall n\, \exists m\, \varphi(n, m)$ to a game whose quantum value is $1$ exactly when the sentence is true. The source works with synchronous games, for which value $1$ can be witnessed by synchronous strategies (a theorem of Helton, Meyer, Paulsen and Satriano and of Kim, Paulsen and Schafhauser that it quotes). A good expansion links the gapless compression theorem.

## Sources

- H. Mousavi, S. S. Nezhadi and H. Yuen, "Nonlocal games, compression theorems, and the arithmetical hierarchy", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022), 1–11, https://doi.org/10.1145/3519935.3519949; read in arXiv:2110.04651v2 (Theorem 1.1, the overview of known results in Section 1, and Lemma 6.8 of arXiv:2110.04651v2, numbering checked against the rendered copy).
- J. Lin, "MIP^co = coRE", Proceedings of the 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 314–322, https://doi.org/10.1145/3798129.3800751; read in arXiv:2510.07162v1 (Theorem 1.1 of arXiv:2510.07162v1), for the later resolution of the gapped commuting-operator problem.
