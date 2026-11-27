# Quadratic-range surjectivity of the canonical Foulkes–Howe map

For every finite-dimensional complex vector space $V$, $a\ge2$, and $b\ge a(a-1)$ there is a unique complex-linear map $\mu:\operatorname{Sym}^b(\operatorname{Sym}^a V)\to\operatorname{Sym}^a(\operatorname{Sym}^b V)$ with the following prescription, and it is surjective. For vectors $v_{ji}\in V$ with $0\le j<b$, $0\le i<a$, it sends $\prod_j(\prod_i v_{ji})$ to

$$\frac{1}{(a!)^b}\sum_{(\sigma_0,\ldots,\sigma_{b-1})\in(S_a)^b}\prod_i\left(\prod_j v_{j,\sigma_j(i)}\right).$$

The products are taken in the indicated symmetric powers, defined as the subspaces of the symmetric algebra spanned by monomials. This is about the canonical averaged map, not an arbitrary surjection or the $a=6,b\ge6$ headline.

## Depends on

- Homogeneous symmetric powers, monomial spanning, and multilinear permutation averaging.

## Proof depends on

- Descent of the formula to symmetric powers, uniqueness on spanning monomials, and the quadratic-threshold surjectivity argument.

## Expansion

Build the homogeneous symmetric-power interface and prove the formula descends. Isolate the rank/surjectivity comparison with the exact threshold; at $a=6$ it yields $b\ge30$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FoulkesHowe.lean#L42-L45) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FoulkesHowe.lean).
