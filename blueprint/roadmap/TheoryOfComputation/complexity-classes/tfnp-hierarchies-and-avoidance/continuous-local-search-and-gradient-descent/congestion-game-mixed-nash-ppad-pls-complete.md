# Babichenko–Rubinstein: mixed Nash equilibria of explicit congestion games are PPAD ∩ PLS-complete and CCLS = PPAD ∩ PLS

In an explicit congestion game each player chooses among explicitly listed subsets of a set of facilities, and the cost of a facility depends only on how many players use it. Let CONGESTION ask, given such a game and $\epsilon$ in binary, for a mixed $\epsilon$-Nash equilibrium: mixed strategies $x_i$ with $u_i(x_i,x_{-i})\ge u_i(a_i,x_{-i})-\epsilon$ for all players $i$ and actions $a_i$. For a smooth $\phi:[0,1]^J\to[0,1]$ let GD-FIXEDPOINT ask for $x$ with $\partial_j\phi(x)\ge-\epsilon$ whenever $x_j>0$ and $\partial_j\phi(x)\le\epsilon$ whenever $x_j<1$.

Then CONGESTION, the identical-interest 5-polytensor game problem, CON-GD-FIXEDPOINT (componentwise concave $\phi$, with concavity-violation triples), KKT for explicitly given polynomials in the sense of Daskalakis–Papadimitriou, and DEG-5-GD-FIXEDPOINT ($\phi$ an explicit sum of componentwise concave degree-5 monomials) are all $\mathsf{PPAD}\cap\mathsf{PLS}$-complete. As a corollary $\mathsf{CCLS}=\mathsf{PPAD}\cap\mathsf{PLS}$, where CCLS is the componentwise-concave variant of CLS.

## Proof sketch

Membership: congestion games are potential games, and the expected Rosenthal potential is a multilinear polynomial on the product of simplices whose approximate gradient fixed points are approximate mixed equilibria. Hardness reduces 2D-GD-FIXEDPOINT, which is $\mathsf{PPAD}\cap\mathsf{PLS}$-complete by the gradient-descent theorem, to these problems: real coordinates are represented in binary by bit-players, an extra veto player who can cancel any suffix of the binary string ensures that some player can always shift a number infinitesimally in either direction, and all utilities are written explicitly as sums of 5-player sub-utilities, giving an identical-interest polytensor game that is itself an explicit congestion game.

## Depends on

- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](continuous-localopt-and-cls.md)
- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)

## Proof depends on

- [KKT, GD-LOCAL-SEARCH, GD-FIXPOINT and GENERAL-CONTINUOUS-LOCALOPT are PPAD ∩ PLS-complete on the unit square](gradient-descent-problems-ppad-pls-complete.md)
- [Nash's theorem](../../../../GameTheory/noncooperative-games/nash-s-theorem/exists-is-mixed-nash.md)
- [Congestion games have pure Nash equilibria](../../../../GameTheory/noncooperative-games/potential-games/congestion-game-exists-is-pure-nash.md)

## Sources

- Yakov Babichenko and Aviad Rubinstein, "Settling the Complexity of Nash Equilibrium in Congestion Games", STOC (2021), arXiv:2012.04327.
- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
