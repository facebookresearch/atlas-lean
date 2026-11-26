# Quantifier rank and rank-$n$ equivalence

The *quantifier rank* $\mathrm{qr}(\varphi)$ of a first-order formula is defined by $\mathrm{qr} = 0$ for atomic formulas, $\mathrm{qr}(\neg\varphi) = \mathrm{qr}(\varphi)$, $\mathrm{qr}(\varphi \circ \psi) = \max(\mathrm{qr}\varphi, \mathrm{qr}\psi)$ for binary connectives (and the supremum for finite conjunctions and disjunctions), and $\mathrm{qr}(\exists x\varphi) = \mathrm{qr}(\forall x\varphi) = \mathrm{qr}(\varphi)+1$. Two structures with distinguished tuples $(\mathfrak{A}, \bar a)$ and $(\mathfrak{B}, \bar b)$ are *$n$-equivalent*, $(\mathfrak{A},\bar a) \equiv_n (\mathfrak{B}, \bar b)$, if they satisfy the same formulas of quantifier rank at most $n$.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
