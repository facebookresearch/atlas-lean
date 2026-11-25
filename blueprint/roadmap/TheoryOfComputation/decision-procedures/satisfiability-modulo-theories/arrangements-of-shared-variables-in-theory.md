# Arrangements of shared variables in theory combination

If $P$ is a partition of a finite set $S$ of variables with equivalence relation $R$, the *arrangement* of $S$ given by $P$ is

$$\mathrm{ar}(S) = \{x = y \mid x, y \in S,\ x R y\} \cup \{x \ne y \mid x, y \in S,\ \text{not } x R y\},$$

read as the conjunction of these equations and disequations; a finite set has finitely many arrangements.

Let $\mathcal{T}_1$ and $\mathcal{T}_2$ be theories with disjoint signatures, let $\varphi_1$ and $\varphi_2$ be $1$-pure and $2$-pure conjunctions of literals, and let $\tilde v$ be the set of variables they share. If $\varphi_1 \wedge \varphi_2$ is satisfiable in $\mathcal{T}_1 \cup \mathcal{T}_2$, then for some arrangement $\mathrm{ar}(\tilde v)$, namely the one induced by a satisfying valuation, $\varphi_i \wedge \mathrm{ar}(\tilde v)$ is satisfiable in $\mathcal{T}_i$ for $i = 1, 2$: the reduct of a model of $\mathcal{T}_1 \cup \mathcal{T}_2$ to the signature of $\mathcal{T}_i$ is a model of $\mathcal{T}_i$.

## Depends on

- [Purification into separate form](purification-into-separate-form.md)

## Sources

- C. Tinelli and M. Harandi, "A new correctness proof of the Nelson–Oppen combination procedure", in *Frontiers of Combining Systems (FroCoS 1996)*, <https://homepage.cs.uiowa.edu/~tinelli/papers/TinHar-FROCOS-96.pdf>, Section 2.1 and Proposition 3.11
