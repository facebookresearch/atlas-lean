# NC1 equals logarithmic formula depth and polynomial formula size

For a language $L\subseteq\{0,1\}^*$ the following are equivalent (nonuniformly): (i) $L\in\mathsf{NC}^1$, i.e. its slices have fan-in-two circuits of polynomial size and depth $O(\log n)$; (ii) its slices have De Morgan formulas of depth $O(\log n)$; (iii) its slices have De Morgan formulas with polynomially many leaves.

## Proof sketch

(i)⇒(ii) by unfolding a circuit into a formula of the same depth; (ii)⇒(iii) since depth $d$ formulas have at most $2^d$ leaves; (iii)⇒(i) by Spira's balancing.

## Depends on

- [The class NC^k](../../../../complexity-classes/time-and-space-complexity-classes/nck.md)
- [Formula-size complexity classes](../../circuit-models-and-classes/nonuniform-circuit-classes/formula-size-complexity-classes.md)

## Proof depends on

- [Unfolding a circuit into a formula of the same depth](../../circuit-models-and-classes/circuit-models-and-complexity-measures/unfolding-a-circuit-into-a-formula.md)
- [Spira's theorem: balancing formulas](spira-formula-balancing.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
