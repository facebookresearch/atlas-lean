# Nechiporuk's subfunction counting lemma

Let $Y$ be a set of variables. A formula over any basis of fan-in at most two whose leaves include exactly $\ell\ge1$ leaves labelled by variables of $Y$ computes at most $16^\ell/4$ distinct subfunctions on $Y$, where a *subfunction on $Y$* is obtained by fixing all variables outside $Y$ to constants. (If $\ell=0$ there are at most two subfunctions.)

## Proof sketch

After fixing the variables outside $Y$, every subformula without $Y$-leaves becomes a constant and every gate with one such argument becomes a unary function of the other, so the subfunction is determined by the at most $\ell-1$ binary gates reading $Y$ on both sides (16 choices each) and by the unary functions on the $\ell$ leaf paths.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady, 1966.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
