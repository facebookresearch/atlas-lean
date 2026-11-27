# Fixed-point logics embed into finite-variable infinitary logic

Every formula of FO(LFP) (and of FO(TC)) whose fixed points and closures range over relations of arity at most $r$ and which uses $v$ distinct first-order variables (counting those bound by the fixed-point and closure operators) is equivalent, on all finite structures, to a formula of $L^{k}_{\infty\omega}$ for some $k$ depending only on $r$ and $v$. Hence queries definable in these logics are invariant under $k$-pebble game equivalence for some fixed $k$.

## Proof sketch

Unfold a least fixed point as the infinite disjunction of its finite stages $\varphi^0 \vee \varphi^1 \vee \dots$ (on a finite structure the stages reach the fixed point after finitely many steps); each stage is obtained by substituting the previous one into the body, reusing the same finitely many variables, so all stages are $k$-variable formulas.

## Depends on

- [Finite-variable logics $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](finite-variable-logics.md)
- [Formulas of first-order logic with least fixed points](../immerman-vardi-theorem/ogfo.md)
- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)

## Proof depends on

- [Pebble games characterize $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](pebble-games-characterize-finite-variable-logic.md)

## Sources

- Ph. G. Kolaitis and M. Y. Vardi, "Infinitary Logics and 0-1 Laws", Information and Computation 98(2), 258–294, 1992.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- N. Immerman, Descriptive Complexity, Springer, 1999.
