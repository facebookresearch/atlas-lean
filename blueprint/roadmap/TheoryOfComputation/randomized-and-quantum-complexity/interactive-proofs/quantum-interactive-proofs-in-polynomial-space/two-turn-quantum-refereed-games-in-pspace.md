# Gutoski-Wu: two-turn quantum refereed games are in PSPACE

The class of problems decided by quantum refereed games in which a polynomial-time quantum referee exchanges one round of quantum messages with each of two competing unbounded provers (one trying to make the referee accept, the other to reject) is contained in, and in fact equals, $\mathrm{PSPACE}$.

## Proof sketch

The value of the game is the value of a min-max problem over two compact sets of density operators (or quantum strategies) of exponential dimension with bilinear payoff. A parallel matrix multiplicative weights method approximates equilibria of such min-max problems with polynomially many rounds of $\mathrm{NC}(\mathrm{poly})$ computations; PSPACE-hardness follows from Feige and Kilian's theorem that one-round classical refereed games capture PSPACE, since a quantum referee simulates a classical one.

## Depends on

- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Regret bound for the matrix multiplicative weights update](matrix-multiplicative-weights-regret-bound.md)
- [Matrix exponentials of exponential-dimension matrices in polynomial depth](matrix-exponentials-in-polynomial-depth.md)
- [Borodin: NC(poly) = PSPACE](borodin-polynomial-depth-equals-polynomial-space.md)

## Sources

- Gus Gutoski, Xiaodi Wu, "Parallel approximation of min-max problems with applications to classical and quantum zero-sum games", CCC (2012); arXiv:1011.2787.
- Uriel Feige, Joe Kilian, "Making games short", STOC (1997).
