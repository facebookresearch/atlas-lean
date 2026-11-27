# Kannan: Σ₂ ∩ Π₂ has languages without circuits of size n^k

For every fixed $k$, there is a language in $\Sigma_2^p\cap\Pi_2^p$ that is not decided by Boolean circuits of size $O(n^k)$.

## Proof sketch

First, a $\Sigma_4^p$ (in fact $\Sigma_3^p$) language: at length $n$, take the lexicographically first truth table on the first $n^{k+1}$ inputs that is not computed by any circuit of size $n^k$ (exists by counting). If $\mathsf{NP}\not\subseteq\mathsf{P}/\mathrm{poly}$ then SAT itself works; otherwise Karp–Lipton collapses $\mathsf{PH}$ to $\Sigma_2^p\cap\Pi_2^p$ and the diagonal language lands there.

## Depends on

- [The class $\Sigma_k^p$](../../time-and-space-complexity-classes/sigma-k.md)
- [The universal levels of the polynomial hierarchy](../../time-and-space-complexity-classes/pi-k.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../../../circuit-complexity/shannon-s-circuit-size-lower-bound/shannon-hard-function.md)
- [Karp-Lipton theorem: NP in P/poly collapses PH](../../karp-lipton.md)

## Sources

- Ravi Kannan, "Circuit-Size Lower Bounds and Non-Reducibility to Sparse Sets", Information and Control 55(1–3), 1982.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
