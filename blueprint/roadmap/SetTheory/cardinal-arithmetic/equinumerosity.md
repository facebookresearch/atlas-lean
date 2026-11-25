# Equinumerous sets

Two sets $A$ and $B$ are equinumerous, written $A \approx B$, when there is a bijection from $A$ onto $B$. Mathlib packages this as an equivalence relation on types. For types $\alpha$ and $\beta$ in the same universe, $\alpha \approx \beta$ holds when there exists a bijection between them, given by a function $\alpha \to \beta$ with a two-sided inverse. This relation is reflexive, symmetric and transitive, through the identity bijection, inverse bijections and composite bijections. It asserts that a bijection exists, without choosing one. Applied to the types of elements of two sets $A$ and $B$, it gives the familiar definition.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
