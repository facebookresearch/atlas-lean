# Exact VP and VNP differ on families with two-n variables

For every field $F$, on the type of families $p_n\in F[X_{(i,b)}:i\in[n],\ b\in\{0,1\}]$, the two predicates $\mathrm{IsVP}$ and $\mathrm{IsVNP}$ are unequal. They both require arity and total degree eventually bounded by $A n^d$ for natural $A,d$. The VP predicate requires at every index a table of a polynomially bounded number of gates, where a gate is addition, subtraction or multiplication of two values among variables, constants and earlier gate values, and the formal polynomial is an available output value. For VNP, one sums a VP verifier family on the disjoint union of the original and a polynomially bounded finite witness type, substituting every Boolean assignment of $0,1$ to the witnesses and leaving the original variables formal. The conclusion is predicate inequality on the specified variable types, not an unrestricted quantifier over variable families or a specific named witness polynomial.

## Depends on

- [Arithmetic circuits](../arithmetic-circuits/arithmetic-circuit.md) for gate sharing and formal polynomial computation; the particular variable types and Boolean summation are as above.

## Proof depends on

- A separating exact VNP family on the fixed variable sets $[n]\times\{0,1\}$, with a witness verifier and a superpolynomial circuit lower bound over each field.

## Expansion

Track the two coordinates and field characteristic through the lower-bound construction and through the formal-polynomial substitutions. Distinguish this restricted family inequality from strict inclusion on the set of all polynomial families. Neither a change of presentation of the standard conjecture nor a field-specific permanent result establishes this exact carrier claim.

## Sources

- OpenAI, [VPVNP.lean, exact classes and `vp_ne_vnp`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VPVNP.lean#L11-L55).
