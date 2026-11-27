# Formal dual matrix multiplication exponent equals one half

Fix a field $F$. For real weights $(a,b,c)$, at each integer $N\ge1$ multiply a $\lceil N^c\rceil\times\lceil N^a\rceil$ matrix by a $\lceil N^a\rceil\times\lceil N^b\rceil$ matrix. A division-free straight-line program uses free input and constant registers, unit-cost binary additions, subtractions and multiplications on previously computed registers, and free output references. Each entry of the output must equal the corresponding entry of the formal matrix product as a polynomial over $F$ in the inputs, even for finite $F$. An exponent $\tau\in\mathbb R$ is admissible if for every real $\varepsilon>0$ there is $C>0$ such that for every $N\ge1$ some formally correct program has cost at most $C N^{\tau+\varepsilon}$. Let $\omega_F(a,b,c)$ be the real infimum of the admissible exponents.

For every field $F$, the supremum in $\mathbb R$ of all $t\in[0,1]$ satisfying $\omega_F(1,1,t)=2$ equals $1/2$. In these formats the varying weight is the outer row dimension $\lceil N^t\rceil$ and the other dimensions are $N$.

## Depends on

- The formal polynomial interpretation and three rounded dimensions above.

## Proof depends on

- [Three-weight exact formula](formal-three-weight-rectangular-exponent.md) and the characterization of the aspect interval where its correction term vanishes.

## Expansion

Check explicitly that $t=0$ is included despite the totalized denominator, that $t=1/2$ still makes the correction zero, and that for $1/2<t\le1$ it is strictly positive. Do not extend the supremum domain by rewriting the definition.

## Related topics

- [The pointwise dual exponent](dual-circuit-exponent.md) varies the inner dimension and allows all nonnegative aspects; comparing it requires separate transport.

## Sources

- OpenAI, [MatrixExponent.lean, `dualExponent`, `formalAlpha` and `dual_exponent`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixExponent.lean#L94-L119).
