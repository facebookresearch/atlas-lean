# Projections compose and are closed under identity

The identity is a quantifier-free projection, and the composition of two first-order projections (respectively two quantifier-free projections) of dimensions $k$ and $l$ is a first-order (respectively quantifier-free) projection of dimension $kl$. Consequently $\le_{\mathrm{fop}}$ and $\le_{\mathrm{qfp}}$ are preorders on ordered queries, closed under complements, and $\le_{\mathrm{qfp}} \subseteq \le_{\mathrm{fop}} \subseteq \le_{\mathrm{fo}}$.

## Proof sketch

Substitute the inner projection into the outer one: an outer guard over the intermediate universe $\{0,\dots,n^k-1\}$ is pulled back to a quantifier-free formula over $k$-tuples (coordinatewise equality, lexicographic order, finite-carry successor, constants), and an outer literal is replaced by the inner case split, whose guards conjoin.

## Depends on

- [First-order and quantifier-free projections](first-order-and-quantifier-free-projections.md)

## Proof depends on

- [Lexicographic order, successor and BIT on tuples are definable](../ordered-structures-and-arithmetic/lexicographic-tuple-numeric-predicates.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
