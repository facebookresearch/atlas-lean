# The exact factor-of-IID threshold for the free Ising law on a regular tree

Let $d\ge3$ and $\beta\ge0$, and put $\theta=\tanh\beta$. Model the infinite $d$-regular tree by the empty word and finite words on $d$ letters with unequal consecutive letters, joining words that differ by appending one letter. For a finite nonempty connected vertex set $A$, the free zero-field law assigns a prescribed spin configuration $\eta$ on $A$ the cylinder probability

$$
\frac12\prod_{\{v,w\}\in E(A)}\frac{1+\theta\eta_v\eta_w}{2},
$$

where spins are in $\{-1,1\}$ and edges of the induced tree are counted once. This law is the pushforward of independent uniform $[0,1]$ vertex labels by a measurable map commuting almost surely with each fixed automorphism if and only if $\theta\le1/\sqrt{d-1}$. Equality is included; no common exceptional set over all automorphisms or finite coding radius is required.

**Conventions.** Use the native regular tree and its full automorphism group, the connected-cylinder free Ising law, and the almost-sure equivariance definition (distinct from pointwise equivariance).

## Depends on

- [The free Ising cylinder law on a regular tree](free-ising-tree-cylinder-law.md)

## Expansion

An obstruction using the spectral/correlation bound for factors of IID, and a factor construction up to the critical equality case. A subcritical construction only for $(d-1)\theta<1$ does not give the stated sufficient range.

Identify the broadcast representation of the free cylinders and verify automorphism invariance. Separate impossibility beyond the threshold from existence at and below it; establish the sharp critical variance and recovery estimates before combining the two directions.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FreeIsing.lean#L87-L90)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/236.md)
- [Accompanying manuscript: The sharp factor-of-IID threshold for the free Ising model on regular trees](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf)
