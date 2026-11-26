# Read-over-write reduction for the theory of arrays

Consider a conjunction $\varphi$ of literals in the quantifier-free theory of arrays with $\mathrm{select}$, $\mathrm{store}$ and extensionality. Flatten $\varphi$ so that every $\mathrm{store}$ term $\mathrm{store}(a, i, v)$ is named by a fresh array constant $b$ with the equation $b = \mathrm{store}(a, i, v)$. Then:

1. replace each disequality $a \ne c$ between arrays by $\mathrm{select}(a, k) \ne \mathrm{select}(c, k)$ for a fresh index constant $k$;
2. for each named store $b = \mathrm{store}(a, i, v)$, add $\mathrm{select}(b, i) = v$ and, for every index term $j$ occurring in the resulting formula, the clause $i = j \vee \mathrm{select}(b, j) = \mathrm{select}(a, j)$;
3. treat $\mathrm{select}$ and $\mathrm{store}$ as uninterpreted functions, keeping the positive array equalities as equalities of uninterpreted terms.

The resulting formula of equality logic with uninterpreted functions is satisfiable if and only if $\varphi$ is satisfiable in the theory of arrays. For example, $a = \mathrm{store}(a, i, 1) \wedge \mathrm{select}(a, i) \ne 1$ is refuted by the added equation $\mathrm{select}(b, i) = 1$ together with $a = b$.

## Proof depends on

- [Congruence closure decides conjunctions of ground equalities](congruence-closure-decides-conjunctions-of.md)
- [Purification into separate form](purification-into-separate-form.md)

## Sources

- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016
- A. R. Bradley and Z. Manna, *The Calculus of Computation: Decision Procedures with Applications to Verification*, Springer, 2007
