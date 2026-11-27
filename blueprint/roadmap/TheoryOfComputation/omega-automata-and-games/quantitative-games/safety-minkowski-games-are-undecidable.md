# Safety Minkowski games are undecidable

In games where players move a point of $\mathbb R^d$ by choosing sets of vectors, the position being updated by Minkowski sums, no algorithm decides whether the first player can keep the point inside a given polytope forever, already with rational polytopes and a trivial opponent.

For $A,B\subseteq\mathbb R^d$ the *Minkowski sum* is $A+B=\{a+b: a\in A, b\in B\}$. In a *Minkowski game* player A has a finite set $\mathcal M_A$ of moves and player B a finite set $\mathcal M_B$, each move being a subset of $\mathbb R^d$. In each round, from position $a$, player A chooses a move $m_A\in\mathcal M_A$ and player B picks the next position $b\in a+m_A$; then player B chooses a move $m_B\in\mathcal M_B$ and player A picks the next position in $b+m_B$. Each player thus resolves the imprecision of the other's moves. A *safety Minkowski game* $\langle\mathcal M_A,\mathcal M_B,S,v_0\rangle$ is won by player A if the position stays in the safe set $S$ forever; it is *single-sided* when player B has only the trivial move $\{0\}$.

**Theorem.** There are a dimension $d$, a rational convex polytope $S$ and a finite family $\mathcal M_A$ of rational closed convex polytopes in $\mathbb R^d$ such that it is undecidable, given a rational initial vector $v_0$, whether player A has a winning strategy in the single-sided safety Minkowski game $\langle\mathcal M_A,S,v_0\rangle$.

In the setting of computable analysis, the source shows that it is semi-decidable whether player B wins a safety Minkowski game when player A's moves are overt sets, player B's moves compact sets and the safe set closed; it also studies boundedness and structural safety Minkowski games.

## Depends on

- [Faces of a convex polytope](../../../Combinatorics/polytopes-simplicial-complexes/faces-of-convex-polytopes/faces.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from a two-counter machine for which existence of an infinite valid computation from given inputs is undecidable (Minsky); its edges are subdivided to simplify the construction. The game is played in $\mathbb R^{4+|Q|}$: two coordinates $y_0,y_1$ encode the counters, two are auxiliary, and one coordinate per control state records the current state, each instruction $e$ from $q_i$ to $q_f$ being a move $A_e^{xy}\times\{a_e^Q\}$ that moves weight from coordinate $q_i$ to $q_f$. To stay safe player A must simulate the machine faithfully, so player A wins iff the machine has an infinite valid computation from the input encoded in $v_0$. The construction first yields a safety-reachability game, which an extra dimension turns into a pure safety game.

## Sources

- Stéphane Le Roux, Arno Pauly and Jean-François Raskin, "Minkowski Games", *ACM Transactions on Computational Logic* 19(3), 2018, article 20, pp. 1–29, doi:[10.1145/3230741](https://doi.org/10.1145/3230741); read in arXiv:1609.07048v2 ([arXiv](https://arxiv.org/abs/1609.07048v2)), cited by section: Section 2 (Minkowski sums, strategies, the definitions of boundedness, safety and structural safety Minkowski games, single-sided games) and Section 7 (the undecidability theorem for one-sided safety Minkowski games with its reduction from two-counter machines).
