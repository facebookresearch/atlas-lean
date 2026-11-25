# Nelson–Oppen combination of decision procedures

A consistent, quantifier-free theory $\mathcal{T}$ with signature $\Sigma$ is *stably infinite* if every quantifier-free $\Sigma$-formula that is satisfiable in $\mathcal{T}$ is satisfiable in an infinite model of $\mathcal{T}$. Let $\mathcal{T}_1$ and $\mathcal{T}_2$ be stably infinite theories with disjoint signatures, let $\varphi_1$ and $\varphi_2$ be $1$-pure and $2$-pure conjunctions of literals, and let $\tilde v$ be the set of variables they share. Then $\varphi_1 \wedge \varphi_2$ is satisfiable in $\mathcal{T}_1 \cup \mathcal{T}_2$ if and only if there is an arrangement $\mathrm{ar}(\tilde v)$ of $\tilde v$ such that $\varphi_i \wedge \mathrm{ar}(\tilde v)$ is satisfiable in $\mathcal{T}_i$ for $i = 1, 2$.

Consequently, if satisfiability of conjunctions of literals is decidable in $\mathcal{T}_1$ and in $\mathcal{T}_2$, it is decidable in $\mathcal{T}_1 \cup \mathcal{T}_2$: put the input in separate form, choose an arrangement of the shared variables, and accept if both component checks succeed for some choice. Stable infiniteness cannot be dropped: if $\mathcal{T}_1$ has only models with at most two elements, the formula $f x \ne f y \wedge g x \ne g z \wedge g y \ne g z$, with $f$ a function symbol of $\mathcal{T}_1$ and $g$ one of a second theory with models of every cardinality, neither forced to be constant, passes the check for the arrangement $\{x \ne y\}$ although it is unsatisfiable in the union.

## Depends on

- [Arrangements of shared variables in theory combination](arrangements-of-shared-variables-in-theory.md)

## Proof depends on

- [Purification into separate form](purification-into-separate-form.md)

## Sources

- C. Tinelli and M. Harandi, "A new correctness proof of the Nelson–Oppen combination procedure", in *Frontiers of Combining Systems (FroCoS 1996)*, <https://homepage.cs.uiowa.edu/~tinelli/papers/TinHar-FROCOS-96.pdf>, Definition 3.3, Propositions 3.8, 3.10 and 3.11 and Corollaries 3.9 and 3.12, and the example in Section 3.2
- Original combination method: G. Nelson and D. C. Oppen, "Simplification by cooperating decision procedures", *ACM Transactions on Programming Languages and Systems* 1(2):245–257, 1979. The statement above follows Tinelli and Harandi, who credit the method to Nelson and Oppen.
