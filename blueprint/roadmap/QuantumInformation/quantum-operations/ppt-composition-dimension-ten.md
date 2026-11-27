# A dimension-ten PPT pair with non-entanglement-breaking composition

For a complex-linear map between matrix algebras, complete positivity means positivity on positive semidefinite block matrices after entrywise block amplification at every positive integer auxiliary size. PPT requires complete positivity of the map and of its output transpose. Entanglement breaking means complete positivity and a separable output for every amplified positive input, with separable meaning a finite sum of tensor products of positive semidefinite matrices.

The following fixed maps on $M_{10}(\mathbb C)$ are PPT. Start with the real $6\times4$ matrices $B_0,\ldots,B_3$, whose rows, separated by semicolons, are

- $B_0$: $(6,0,0,0);(0,6,0,0);(0,0,6,0);(0,0,0,6);(0,0,0,0);(0,0,0,0)$.
- $B_1$: $(-12,0,0,0);(0,-6,0,0);(0,0,6,0);(0,0,0,12);(-6,0,6,6);(-6,-6,6,0)$.
- $B_2$: $(0,6,-2,0);(6,6,0,2);(-2,0,10,0);(0,2,0,24);(0,0,0,6);(0,-6,6,-6)$.
- $B_3$: $(0,0,-4,-3);(0,-2,-3,-4);(-4,-3,11,6);(-3,-4,6,25);(6,6,0,0);(0,-6,6,6)$.

Define $F(X)=\sum_{ij}X_{ij}B_i^\mathsf T B_j$. Let $S$ and $A$ be the usual symmetric and antisymmetric isometries into $\mathbb C^4\otimes\mathbb C^4$, with symmetric pairs ordered lexicographically with diagonal included and antisymmetric pairs ordered lexicographically with distinct entries. The off-diagonal vectors are $(e_i\otimes e_j\pm e_j\otimes e_i)/\sqrt2$ for $i<j$. Let $E(X)=A^*(F\otimes F)(SXS^*)A$, let $J$ be the reversal on the six exterior coordinates with signs $(1,-1,1,1,-1,1)$, and let $I:\mathbb C^6\hookrightarrow\mathbb C^{10}$ include the first six coordinates. The specified maps are $\Phi_1(X)=IE(X^\mathsf T)I^*$ and $\Phi_2(Y)=G^*(I^*YI)$, where $G(X)=J E(X)^\mathsf T J^*$ and $G^*$ is its Hilbert–Schmidt adjoint. Their composition is not entanglement breaking, and its Choi matrix $Z=[(\Phi_2\Phi_1)(e_{ij})]_{ij}$ is nonzero with no nonzero vector $u\otimes v$ in its range.

## Depends on
- [Complete positivity](../../Analysis/operator-algebras/completely-positive-maps/completely-positive-map.md), with the finite block-amplification model and output-transpose convention.

Use the declared exact matrices and basis order, not arbitrary witnesses of dimension ten.

## Proof depends on
Exact positivity certificates for the maps and their output transposes, and exclusion of product vectors from the composite Choi range.

## Expansion
Verify the matrices and isometries and the adjoint formula first. Then give the rank/product-vector certificate and the step from nonzero Choi with product-free range to failure of the positive-tensor decomposition. These maps are not required to preserve trace.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DimensionTenPair.lean#L112-L121) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/272.md).
