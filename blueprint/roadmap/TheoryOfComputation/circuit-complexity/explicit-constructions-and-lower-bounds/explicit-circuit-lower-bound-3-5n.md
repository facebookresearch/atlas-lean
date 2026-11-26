# Mishra–Santhanam: a function in P requiring 3.5N − o(N) gates over B₂

Every Boolean circuit over the full binary basis $B_2$ (all two-input gates) computing an affine disperser for dimension $d$ on $N$ bits has at least $3.5N-7d$ gates. Combined with an explicit affine disperser for dimension $d=O(N/\log N)$ computable in polynomial time, there is a language in $\mathsf{P}$ whose slices of length $N$ require

$$
3.5N-\frac{42N}{\lfloor\log_2N\rfloor+1}-7
$$

gates over $B_2$ for all large $N$.

## Proof sketch

Gate elimination: repeatedly fix an affine restriction (a linear equation) that eliminates on average $3.5$ gates, using a refined potential argument that handles degenerate gate configurations; an affine disperser stays non-constant until the dimension drops below $d$, so at least $(N-d)$ restrictions are possible.

## Depends on

- [Affine dispersers](../gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Proof depends on

- [An explicit polynomial-time affine disperser for dimension O(N^{4/5})](explicit-affine-disperser.md)

## Sources

- Om Swostik Mishra and Rahul Santhanam, "An Explicit 3.5n - o(n) Size Lower Bound against General Boolean Circuits", Electronic Colloquium on Computational Complexity, report TR26-260, 2026, Theorem 4.1.
- Eli Ben-Sasson and Swastik Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing 41(4), 2012.
