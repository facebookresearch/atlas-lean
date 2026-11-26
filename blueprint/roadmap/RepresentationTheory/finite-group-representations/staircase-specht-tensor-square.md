# The Saxl tensor-square positivity statement

For every $m\ge1$, let $\lambda$ be the staircase diagram with zero-based cells $(i,j)$ satisfying $i+j<m$. For every diagram $\mu$ of the same size, $\dim_{\mathbb C}\operatorname{Hom}_{S_{|\lambda|}}(S^\mu,S^\lambda\otimes S^\lambda)>0$. For a Young diagram and a canonical tableau on its boxes, take the complex permutation space on words recording the row assignment. In that space take the alternating sum of the column-stabilizer translates of the tableau’s row-word basis vector and span its orbit under the whole symmetric group. This is the Specht representation $S^\lambda$ used here. Multiplicities are complex dimensions of equivariant linear maps into tensor products with the diagonal action.

## Depends on

- Polytabloids in the row-tabloid permutation space, Specht modules and diagonal tensor products.

## Proof depends on

- The staircase-specific positivity argument for all partitions, not existential universality of some other partition.

## Expansion

Prove agreement of the comparator’s orbit-span model with standard Specht representations, then isolate the Kronecker positivity step. The one-box staircase is included.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Saxl.lean#L112-L114) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Saxl.lean).
