# A cubic lower bound for border determinants of the permanent

Let $P_m=\sum_{\sigma\in S_m}\prod_{i=0}^{m-1}X_{i,\sigma(i)}$ be the $m\times m$ permanent, with $m\ge1408$. If $P_m$ has a size-$n$ border determinant, then $m^3/(5529600e)\le n$. A size-$n$ border determinant means $n>0$ and a sequence of determinants of $n\times n$ complex affine-linear pencils, convergent to the polynomial coefficient by coefficient (for every monomial). A size-$n$ exact determinant means $n>0$ and equality with one determinant of such a pencil.

## Depends on

- Multivariable coefficients, determinant of an affine pencil, and coefficientwise limits over $\mathbb C$.

## Proof depends on

- The permanent selector specialization and critical-dimension estimate over the algebraic closure of $\mathbb F_2$, transported to the size bound for complex affine pencils.

## Expansion

Derive the selector lower bound from the critical-dimension estimate and compare the auxiliary size to $m$. Verify the explicit threshold $1408$ and constant $5529600e$. The general smooth-initial-form estimate in the companion result is not a substitute for the selector estimate.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PermanentCubic.lean#L33-L39) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PermanentCubic.lean).
