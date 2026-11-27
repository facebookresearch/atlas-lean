# Exact three-weight rectangular exponent for formal matrix multiplication

Fix a field $F$. For real weights $(a,b,c)$, at each integer $N\ge1$ multiply a $\lceil N^c\rceil\times\lceil N^a\rceil$ matrix by a $\lceil N^a\rceil\times\lceil N^b\rceil$ matrix. A division-free straight-line program uses free input and constant registers, unit-cost binary additions, subtractions and multiplications on previously computed registers, and free output references. Each entry of the output must equal the corresponding entry of the formal matrix product as a polynomial over $F$ in the inputs, even for finite $F$. An exponent $\tau\in\mathbb R$ is admissible if for every real $\varepsilon>0$ there is $C>0$ such that for every $N\ge1$ some formally correct program has cost at most $C N^{\tau+\varepsilon}$. Let $\omega_F(a,b,c)$ be the real infimum of the admissible exponents.

For all $a,b,c\in\mathbb R$, sort $\max(a,0),\max(b,0),\max(c,0)$ as $x\ge y\ge z\ge0$. Then

$$
\omega_F(a,b,c)=x+y+\frac{\max(0,(x+y)z-xy)^2}{4xyz}.
$$

Division is totalized with division by zero returning zero, so the correction term vanishes on the coordinate planes of the clipped weights. At nonpositive weight the ceiling dimension is one for positive integer $N$.

## Depends on

- The division-free program model with formal polynomial correctness and real admissible exponents above.

## Proof depends on

- Matching lower and upper estimates for formal matrix-product cost in the three-weight model, with rounding, degeneracies and arbitrary characteristic, plus nonemptiness and boundedness of the real infimum domain.

## Expansion

Separate clipping and weight permutations from the positive-coordinate case, and give the sharp upper and lower reductions for the latter. Develop the formal polynomial circuit evaluator before considering a bridge to field-point computations; equality of functions on a finite field cannot establish arbitrary polynomial equality.

## Related topics

- [The one-aspect exponent](rectangular-circuit-exponent.md) uses pointwise correctness and is not an interchangeable definition.

## Sources

- OpenAI, [MatrixExponent.lean, formal correctness, admissibility and `rectangular_exponent`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixExponent.lean#L13-L132).
