# Nash equilibria in symmetric game networks with partial observation are undecidable

Whether a symmetric game network, in which identical players each observe the global state only partially, has a (symmetric) Nash equilibrium is undecidable for LTL objectives with any fixed number of at least three players, while for bounded-memory strategies it is EXPSPACE-complete.

**Setting.** An *$n$-player game network* $\mathcal G=\langle G,(\equiv_i)_{i<n},(\Omega_i)_{i<n}\rangle$ consists of a one-player arena $G$ with finitely many states and actions, an equivalence relation $\equiv_i$ on configurations in $\mathrm{States}^n$ for each player $i$, the configurations player $i$ cannot distinguish, and an objective $\Omega_i\subseteq(\mathrm{States}^n)^\omega$ for each player that respects $\equiv_i$. The game is played on the product of $n$ copies of $G$, each player moving in its own copy, and a strategy of player $i$ must choose the same action after $\equiv_i$-equivalent histories. The network is *symmetric* if permutations $\pi_{i,j}$ of the players with $\pi_{i,j}(i)=j$, composing consistently, carry the observation relation and the objective of player $i$ to those of player $j$; a strategy profile is *symmetric* if $\sigma_i(\rho)=\sigma_j(\rho(\pi_{i,j}^{-1}))$ for all players and histories. A profile is a *Nash equilibrium* if no player who loses under it can win by changing only its own strategy. The *existence problem* asks whether a (symmetric) Nash equilibrium exists from a given configuration; the *positive existence problem* asks for one in which all players win.

**Theorem (Bouyer, Markey and Vester).**

1. For every fixed number $n\ge3$ of players, the existence of a (symmetric) Nash equilibrium in symmetric $n$-player game networks with LTL objectives is undecidable (Theorem 16). Here an instance is finite: the one-player arena is given by its finite sets of states and actions and its tables $\mathrm{Mov}$ and $\mathrm{Tab}$, each $\equiv_i$ by its finite set of pairs of configurations in $\mathrm{States}^n$, the symmetric representation by the permutations $\pi_{i,j}$, the objectives by LTL formulas over atoms that are states of the players' copies, and the initial configuration by a tuple of states.
2. The existence and the positive existence of a *parameterized* symmetric Nash equilibrium for LTL objectives, a single strategy that yields a Nash equilibrium for every number of players, are undecidable, even for memoryless strategies (Theorem 12, whose "(positive) existence" covers both problems). For this item the observation relations, which must be defined for every number of players, are given by templates whose size does not depend on $n$, such as perfect observation of a fixed set of players and none of the others; the source fixes no general template language.

The source also states that the (constrained) existence of a symmetric Nash equilibrium is undecidable already for two players with perfect information when the objectives may be non-regular sets of plays (Theorem 11), encoding the runs of a two-counter machine; it does not say how non-regular objectives are given as input, so that statement is not part of the theorem here.

In contrast, the existence of a bounded-memory symmetric Nash equilibrium for LTL objectives, with or without positivity and constraints, is EXPSPACE-complete (Theorem 14). Existence is at least as hard as positive existence (Proposition 13), and symmetric equilibria are at least as hard to find as arbitrary ones (Proposition 10).

## Depends on

- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Satisfaction of LTL formulas on ω-words](../../../Logic/temporal-logic/linear-temporal-logic/satisfies.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof adapts Pnueli and Rosner's proof that distributed synthesis of reactive systems with LTL specifications under imperfect information is undecidable, adding a matching-pennies module at the start so that sure-winning strategies become Nash equilibria; it is only outlined in the refereed version read. A good expansion links a page for the undecidability of distributed synthesis for LTL specifications. For the parameterized result and the one stated in prose, Theorem 11 encodes the runs of a two-counter machine into non-regular objectives of a two-player game, and Theorem 12 encodes a Turing machine into game networks with arbitrarily many players, each player controlling one cell of the tape, with LTL formulas enforcing a correct simulation.

## Sources

- Patricia Bouyer, Nicolas Markey and Steen Vester, "Nash equilibria in symmetric graph games with partial observation", *Information and Computation* 254, pp. 238–258, 2017, doi:[10.1016/j.ic.2016.10.010](https://doi.org/10.1016/j.ic.2016.10.010), the journal version of the same work, listed as background; it was not read, and the statements here follow the SR 2014 version, which was read.
- Patricia Bouyer, Nicolas Markey and Steen Vester, "Nash equilibria in symmetric games with partial observation", in *Proceedings of the 2nd International Workshop on Strategic Reasoning (SR 2014)*, Electronic Proceedings in Theoretical Computer Science 146, pp. 49–55, 2014, doi:[10.4204/EPTCS.146.7](https://doi.org/10.4204/EPTCS.146.7); read in arXiv:1404.0839v1 ([arXiv](https://arxiv.org/abs/1404.0839v1)), the published version, whose numbering is used: the definitions of arenas, game networks, symmetric game networks and symmetric profiles in Section 2.1, Problem 1 and Proposition 10, and Theorems 11, 12, 14 and 16 and Proposition 13 in Section 3, with the proof outlines that accompany Theorems 12 and 16.
