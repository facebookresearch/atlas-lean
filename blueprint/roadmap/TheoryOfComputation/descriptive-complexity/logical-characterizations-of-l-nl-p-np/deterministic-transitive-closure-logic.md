# Deterministic transitive closure logic FO(DTC)

For a formula $\varphi(\bar x,\bar y)$ with $\bar x,\bar y$ $k$-tuples, its **deterministic reduct** is $\varphi_d(\bar x,\bar y)=\varphi(\bar x,\bar y)\wedge\forall\bar z\,(\varphi(\bar x,\bar z)\to\bar z=\bar y)$, the edges out of vertices of out-degree exactly one. $\mathrm{FO(DTC)}$ extends first-order logic by formulas $\mathrm{DTC}[\varphi](\bar s,\bar t)$, true iff $(\bar s,\bar t)$ is in the reflexive transitive closure of $\varphi_d$; the operator may be nested and occur at any polarity.

## Depends on

- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)
- [Ordered finite structures with built-in numerical predicates](ordered-structures-with-bit.md)

## Sources

- Neil Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 1987.
- Neil Immerman, "Descriptive Complexity", Springer, 1999.
