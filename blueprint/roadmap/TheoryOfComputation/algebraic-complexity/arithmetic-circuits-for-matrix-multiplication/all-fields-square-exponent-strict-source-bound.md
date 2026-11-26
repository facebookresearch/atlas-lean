# Strict square matrix multiplication bound over every field, in the pointwise model

For a field $F$, let $\omega_{\mathrm{pt}}(F)$ be the infimum in $\mathbb R$ of the real $\tau$ with the following property: for every $\varepsilon>0$ there is $C>0$ such that for every integer $n\ge1$ there is a straight-line program computing the product on **every pair of** $n\times n$ matrices with entries in $F$, with at most $C n^{\tau+\varepsilon}$ charged gates. Programs extend a list of registers using either a free field constant or input reference, or one binary $+,-,\times$ on earlier registers (unit cost). Each matrix entry is an arbitrary output register reference, free. Correctness is pointwise even over finite fields; there is no formal polynomial identity condition.

For every field $F$,

$$
\omega_{\mathrm{pt}}(F)<\frac{2371054886006746}{10^{15}}<\frac{2371056}{10^6}.
$$

## Depends on

- The all-positive-size division-free operation model, pointwise evaluation and real admissible-exponent infimum above.

## Proof depends on

- A division-free circuit construction below the first exact rational threshold in all characteristics, including its size and positive-slack bounds. The second strict comparison is exact rational arithmetic.

## Expansion

Erase free register steps to a circuit DAG and reinsert them in the opposite direction; preserve the count of charged operations and all output entries. Pad the finitely many small sizes with the naïve circuits and justify transport of the bounded, nonempty admissible set to the real infimum. Verify the quantitative certificate. This bound is stricter than the [Dupont–Eisenberger et al. bound](../matrix-multiplication-exponent/dupont-eisenberger-et-al2026-upper.md); it does not assert the distinct formal-polynomial exponent equality.

## Related topics

- [The formal square exponent equality](formal-square-exponent-nine-fourths.md) would imply the pointwise upper bound: evaluating a formal identity gives pointwise correctness over the same field, and $9/4$ is below the first threshold. No converse over finite fields is asserted. The pointwise endpoint can also be developed independently via its own source certificate.

## Sources

- OpenAI, [MatrixFields.lean, gate model, pointwise correctness, admissibility and `omega_lt_source_constant`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixFields.lean#L15-L112).
