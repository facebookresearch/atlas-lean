# Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility

On queries over relational vocabularies on ordered structures of size at least $2$:

1. $\le_{\mathrm{fop}}$ and $\le_{\mathrm{qfp}}$ are reflexive and transitive; the one-dimensional identity interpretation is a quantifier-free projection, and the composite of two first-order (quantifier-free) projections is again a first-order (quantifier-free) projection of dimension equal to the product of the dimensions;
2. both are closed under complement: $K \le K'$ implies $\overline{K} \le \overline{K'}$;
3. $K \le_{\mathrm{qfp}} K'$ implies $K \le_{\mathrm{fop}} K'$, which implies $K \le_{\mathrm{fo}} K'$.

## Proof sketch

For composition, substitute the inner projection formulas for the input literals of the outer one (negating when the outer literal is negative), and pull each outer numeric guard back from $\{0, \ldots, n^{k}-1\}$ to $k$-tuples: for first-order projections the lexicographic rank arithmetic is first-order definable with $\le$ and $\mathrm{BIT}$, and for quantifier-free guards over successor and endpoints the translation to tuples needs neither quantifiers nor $\mathrm{BIT}$. Mutual exclusivity of the cases is preserved, so the result is again a projection. Complement closure uses the same interpretation; refinement holds because projections are interpretations.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](first-order-and-quantifier-free-projections.md)

## Sources

- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
- Neil Immerman, "Descriptive Complexity", Graduate Texts in Computer Science, Springer, 1999.
