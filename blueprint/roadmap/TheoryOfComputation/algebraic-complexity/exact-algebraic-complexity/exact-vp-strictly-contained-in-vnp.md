# Strict inclusion of exact VP in VNP over every field

For each field $F$, consider all families of formal polynomials, with a varying finite variable type $X_n$ at index $n$, such that arity and total degree are eventually bounded by $A n^d$ for suitable natural constants. A family is in exact $\mathsf{VP}$ if at each index an exact straight-line circuit computes its formal polynomial with size bounded polynomially in the index. A circuit charges one for each binary $+,-,\times$ on variables, constants or earlier outputs, allows sharing, and takes its result from any available value.

A family $p$ is in $\mathsf{VNP}$ if, also satisfying the arity and degree bounds, it has finite witness types $W_n$ of polynomially bounded cardinality and an exact $\mathsf{VP}$ verifier family $g_n$ over $X_n\sqcup W_n$ such that $p_n$ is the sum of the formally specialized $g_n$ over all maps $W_n\to\{0,1\}$, leaving the $X_n$ variables free. Then $\mathsf{VP}(F)\subsetneq\mathsf{VNP}(F)$ as sets of these families. This neither assumes characteristic zero nor uses evaluation-only equality in small characteristic.

## Depends on

- The formal polynomial, shared gate and finite Boolean summation models above.

## Proof depends on

- Inclusion by summation over an empty witness set and a VNP family with no polynomial-size exact circuit over the chosen field.

## Expansion

Isolate the Boolean-summation inclusion and the lower bound for the separating family. Relate exact polynomial-degree-bounded circuits to the multiplicatively disjoint presentation before identifying the standard conjecture page with this target. The [fixed-arity endpoint](exact-vp-ne-vnp-on-two-n-variables.md) supplies a separately stated inequality on a restricted carrier, not a definitional equality of the two statements.

## Related topics

- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md) uses a multiplicatively disjoint circuit presentation. A comparison requires a model bridge.

## Sources

- OpenAI, [exact VP and VNP classes](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArithmeticHierarchy.lean#L11-L43), [family carriers and third strict inclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArithmeticHierarchy.lean#L179-L212).
