# First-order reductions preserve definability

If $K \le_{\mathrm{fo}} K'$ and $K'$ is definable in first-order logic (respectively in existential second-order logic, in FO(LFP), or in FO(TC)), then $K$ is definable in the same logic. In particular a class that first-order reduces to a first-order definable class is first-order definable, and lower bounds on definability transfer upward along reductions.

## Proof sketch

Pull back the defining sentence along the interpretation; for second-order and fixed-point logics a relation variable of arity $r$ becomes one of arity $rd$, and fixed points are pulled back blockwise.

## Depends on

- [First-order and quantifier-free reductions](first-order-reductions.md)

## Proof depends on

- [Pullback of formulas along interpretations](pullback-along-interpretations.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
