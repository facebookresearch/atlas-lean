# Nechiporuk's subfunction counting lemma

Let $Y$ be a set of variables. A formula over any basis of fan-in at most two whose leaves include exactly $\ell\ge1$ leaves labelled by variables of $Y$ computes at most $16^\ell/4$ distinct subfunctions on $Y$, where a *subfunction on $Y$* is obtained by fixing all variables outside $Y$ to constants. (If $\ell=0$ there are at most two subfunctions.)

## Proof sketch

After fixing the variables outside $Y$, every subformula without $Y$-leaves becomes a constant and every gate with one such argument becomes a unary function of the other, so the subfunction is computed by a fixed tree whose $\ell$ leaves are the $Y$-leaves and whose at most $\ell-1$ inner nodes are the gates with $Y$-leaves on both sides. Each unary function ($0$, $1$, identity or negation) on an edge into such a node is absorbed into the node's two-argument Boolean function (16 choices), leaving only the unary function above the topmost node (4 choices); this gives at most $4\cdot 16^{\ell-1}=16^\ell/4$ subfunctions.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady 7(4), 999–1000, 1966.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
