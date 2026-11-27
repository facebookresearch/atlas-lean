# Dutta multiplicity bounds Hilbert–Samuel multiplicity for complete domains

Let $(R,\mathfrak m)$ be a complete Noetherian local domain of prime characteristic $p$, with $d=\dim R$. Let $F$ be a cochain complex of finite free $R$-modules supported in degrees $-d$ through $0$, with all homology of finite length and $H^0(F)\ne0$. Let $F_n$ be extension of scalars on $F$ along the $n$-fold Frobenius. Every $H^i(F_n)$ has finite length. The sequence $p^{-nd}\sum_{i=0}^d(-1)^i\operatorname{length}_R H^{-i}(F_n)$ converges. Its totalized filter-limit value is at least the comparator's base-ring multiplicity term

$$
\operatorname{limUnder}_{N\to\infty}\frac{d!\,\operatorname{length}_R(R/\mathfrak m^N)}{N^d}.
$$

Here $\operatorname{limUnder}$ is the real-valued filter-limit operator, including its default convention when there is no limit. Only convergence of the Frobenius Euler sequence is a conclusion of this endpoint. The formula uses the natural projection of each module length, and $d$ is the natural projection of Krull dimension after replacing a bottom value by zero.

## Depends on

- Local ring dimension and module length, Frobenius extension of scalars on complexes, and the two multiplicity normalizations.

## Proof depends on

- Preservation of finite-length homology, convergence of the normalized Euler sequence, and the complete-domain comparison inequality.

## Expansion

Build separate lemmas for finite length and convergence before comparing the limits. Keep equicharacteristic prime characteristic, the exact support interval, and the nonzero top homology.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DuttaDomain.lean#L74-L75) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DuttaDomain.lean).
