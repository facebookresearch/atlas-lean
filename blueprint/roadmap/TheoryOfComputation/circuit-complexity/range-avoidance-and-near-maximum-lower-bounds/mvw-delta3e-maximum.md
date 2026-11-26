# Miltersen–Vinodchandran–Watanabe: Delta3E requires near-maximum circuit size

The class $\Delta_3\mathrm{E} = \mathrm{E}^{\Sigma_2\mathrm{P}}$ contains a language whose circuit complexity is at least $2^{n}/n$ on every sufficiently large input length $n$. Before the range avoidance approach, $\Delta_3\mathrm{E}$ was the smallest uniform class known to require exponential circuit size, while classes such as $\Sigma_2\mathrm{E}$ were only known to require half-exponential size.

## Proof sketch

By counting, some truth table on $n$ bits has circuit complexity above $2^n/n$. Whether a given prefix extends to such a truth table is a $\Sigma_2$ question of size $2^{O(n)}$ (there exists an extension such that every small circuit disagrees with it), so binary search over prefixes with a $\Sigma_2\mathrm{P}$ oracle constructs the lexicographically first hard truth table in time $2^{O(n)}$, and the language outputs its bits.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](../symmetric-exponential-time-circuit-lower-bounds/symmetric-alternation-s2p-s2e.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Proof depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](../symmetric-exponential-time-circuit-lower-bounds/symmetric-alternation-s2p-s2e.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- P. B. Miltersen, N. V. Vinodchandran, O. Watanabe, "Super-polynomial versus half-exponential circuit size in the exponential hierarchy", COCOON (1999).
