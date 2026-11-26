# Gutoski-Wu: two-turn quantum refereed games are in PSPACE

The class of problems decided by quantum refereed games in which a polynomial-time quantum referee exchanges one round of quantum messages with each of two competing unbounded provers (one trying to make the referee accept, the other to reject) is contained in, and in fact equals, $\mathrm{PSPACE}$.

## Proof sketch

The value of the game is the value of a min-max problem over two compact sets of density operators (or quantum strategies) of exponential dimension with bilinear payoff. A parallel matrix multiplicative weights method approximates equilibria of such min-max problems with polynomially many rounds of $\mathrm{NC}(\mathrm{poly})$ computations; hardness follows since $\mathrm{PSPACE} = \mathrm{QIP}$ is captured by games with a trivial second prover.

## Depends on

- [Regret bound for the matrix multiplicative weights update](matrix-multiplicative-weights-regret-bound.md)
- [Matrix exponentials of exponential-dimension matrices in polynomial depth](matrix-exponentials-in-polynomial-depth.md)
- [Borodin: NC(poly) = PSPACE](borodin-polynomial-depth-equals-polynomial-space.md)
- [QIP = PSPACE](qip-equals-pspace.md)

## Proof depends on

- [Regret bound for the matrix multiplicative weights update](matrix-multiplicative-weights-regret-bound.md)
- [Matrix exponentials of exponential-dimension matrices in polynomial depth](matrix-exponentials-in-polynomial-depth.md)
- [Borodin: NC(poly) = PSPACE](borodin-polynomial-depth-equals-polynomial-space.md)
- [QIP = PSPACE](qip-equals-pspace.md)

## Sources

- Gus Gutoski, Xiaodi Wu, "Parallel approximation of min-max problems with applications to classical and quantum zero-sum games", CCC (2012); arXiv:1011.2787.
