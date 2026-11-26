# First-order logic with deterministic transitive closure

The *deterministic reduct* of a binary relation $E$ on $k$-tuples keeps an edge $\bar u \to \bar v$ only if $\bar v$ is the unique $E$-successor of $\bar u$. FO(DTC) has the syntax of FO(TC), with formulas $[\mathrm{dtc}_{\bar x, \bar y}\, \varphi](\bar s, \bar t)$, but the closure operator denotes the reflexive–transitive closure of the deterministic reduct of the relation defined by $\varphi$: from $\bar s$ follow the unique successor as long as one exists. Every FO(DTC) formula is equivalent to an FO(TC) formula, obtained by defining the deterministic reduct in first-order logic.

## Depends on

- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)

## Sources

- N. Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 760–778, 1987.
- N. Immerman, Descriptive Complexity, Springer, 1999.
