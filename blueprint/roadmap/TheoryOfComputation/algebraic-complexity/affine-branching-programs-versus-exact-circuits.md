# Strict separation of affine branching programs from exact arithmetic circuits

For any field $F$, use formal polynomial families over finite variable types that vary with the natural family index, with arity and total degree each eventually bounded by a natural polynomial monomial. Let $\mathsf{VBP}$ use polynomial-size topologically ordered affine branching programs (one source of value $1$, affine labels, sum of incoming products, a designated output, counting vertices plus edges). Let $\mathsf{VP}$ use polynomial-size exact straight-line circuits: each charged binary gate adds, subtracts or multiplies two formal polynomials available as variables, constants or earlier gate outputs, and the output is an available polynomial. Gates may be reused and constants, variables and output references are free. Exact correctness is equality of formal polynomials at every family index. An affine branching program is a finite DAG in topological order with source value $1$, each later vertex valued by the sum of predecessor values times the affine-linear labels on incoming edges, and a designated output vertex. A vertex with no incoming edges other than the source has value zero. Size counts vertices plus edges, with parallel edges counted separately.

Then $\mathsf{VBP}(F)\subsetneq\mathsf{VP}(F)$.

## Depends on

- The affine and exact polynomial evaluation models above.

## Proof depends on

- An exact affine-program-to-circuit compilation (including finite-arity expansion cost) and a family computable by polynomial-size circuits but of non-polynomial branching-program size over the same field.

## Expansion

Verify polynomial rather than pointwise semantics for the native circuit, expand affine edge labels with polynomial overhead, and isolate the characteristic-uniform family and its ABP size obstruction.

## Sources

- OpenAI, [ArithmeticHierarchy.lean, exact circuits, affine programs and second strict inclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArithmeticHierarchy.lean#L11-L212).
