# Nash equilibria in symmetric game networks with partial observation are undecidable

Whether a symmetric game network, in which identical players each observe the global state only partially, has a (symmetric) Nash equilibrium is undecidable for LTL objectives with three or more players, while for bounded-memory strategies it is EXPSPACE-complete.

**Setting.** An *$n$-player game network* $\mathcal G=\langle G,(\equiv_i)_{i<n},(\Omega_i)_{i<n}\rangle$ consists of a one-player arena $G$ with finitely many states and actions, an equivalence relation $\equiv_i$ on configurations in $\mathrm{States}^n$ for each player $i$, the configurations player $i$ cannot distinguish, and an objective $\Omega_i\subseteq(\mathrm{States}^n)^\omega$ for each player that respects $\equiv_i$. The game is played on the product of $n$ copies of $G$, each player moving in its own copy, and a strategy of player $i$ must choose the same action after $\equiv_i$-equivalent histories. The network is *symmetric* if permutations $\pi_{i,j}$ of the players with $\pi_{i,j}(i)=j$, composing consistently, carry the observation relation and the objective of player $i$ to those of player $j$; a strategy profile is *symmetric* if $\sigma_i(\rho)=\sigma_j(\rho(\pi_{i,j}^{-1}))$ for all players and histories. A profile is a *Nash equilibrium* if no player who loses under it can win by changing only its own strategy. The *existence problem* asks whether a (symmetric) Nash equilibrium exists from a given configuration; the *positive existence problem* asks for one in which all players win.

**Theorem (Bouyer, Markey and Vester).**

1. For non-regular objectives, the existence of a symmetric Nash equilibrium, also with constraints on which players win or lose, is undecidable already in two-player symmetric game networks with perfect information (Theorem 1).
2. The positive existence of a *parameterized* symmetric Nash equilibrium for LTL objectives, a single strategy that yields a Nash equilibrium for every number of players, is undecidable, even for memoryless strategies (Theorem 2).
3. For LTL objectives, the existence of a (symmetric) Nash equilibrium in symmetric game networks is undecidable for every number $n\ge3$ of players (Theorem 4).

In contrast, the existence of a bounded-memory symmetric Nash equilibrium for LTL objectives, with or without positivity and constraints, is EXPSPACE-complete (Theorem 3). Existence is at least as hard as positive existence (Proposition 2), and symmetric equilibria are at least as hard to find as arbitrary ones (Proposition 1).

## Depends on

- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Satisfaction of LTL formulas on ω-words](../../../Logic/temporal-logic/linear-temporal-logic/satisfies.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Part 1 encodes the runs of a two-counter machine into non-regular objectives of a two-player game. Part 2 encodes a Turing machine into game networks with arbitrarily many players, each player controlling one cell of the tape, with LTL formulas enforcing a correct simulation; the machine halts if and only if for some number of players the play reaches the halting state. Part 3 adapts Pnueli and Rosner's proof that distributed synthesis of reactive systems with LTL specifications under imperfect information is undecidable, adding a matching-pennies module at the start so that sure-winning strategies become Nash equilibria. The proofs are only outlined in the refereed version read; a good expansion links a page for the undecidability of distributed synthesis for LTL specifications, which has none yet.

## Sources

- Patricia Bouyer, Nicolas Markey and Steen Vester, "Nash equilibria in symmetric graph games with partial observation", *Information and Computation* 254, pp. 238–258, 2017, doi:[10.1016/j.ic.2016.10.010](https://doi.org/10.1016/j.ic.2016.10.010) (cited, not read).
- Patricia Bouyer, Nicolas Markey and Steen Vester, "Nash equilibria in symmetric games with partial observation", in *Proceedings of the 2nd International Workshop on Strategic Reasoning (SR 2014)*, Electronic Proceedings in Theoretical Computer Science 146, pp. 49–55, 2014, doi:[10.4204/EPTCS.146.7](https://doi.org/10.4204/EPTCS.146.7); read in arXiv:1404.0839v1 ([arXiv](https://arxiv.org/abs/1404.0839v1)), the published version, whose numbering is used: the definitions of arenas, game networks, symmetric game networks and symmetric profiles in Section 2.1, Problem 1, Propositions 1 and 2, and Theorems 1–4 in Section 3, with the proof outlines that accompany Theorems 2 and 4.
