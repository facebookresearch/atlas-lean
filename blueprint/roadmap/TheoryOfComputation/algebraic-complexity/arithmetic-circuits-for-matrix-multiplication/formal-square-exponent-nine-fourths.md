# Formal square matrix multiplication exponent equals nine fourths

Fix a field $F$. For real weights $(a,b,c)$, at each integer $N\ge1$ multiply a $\lceil N^c\rceil\times\lceil N^a\rceil$ matrix by a $\lceil N^a\rceil\times\lceil N^b\rceil$ matrix. A division-free straight-line program uses free input and constant registers, unit-cost binary additions, subtractions and multiplications on previously computed registers, and free output references. Each entry of the output must equal the corresponding entry of the formal matrix product as a polynomial over $F$ in the inputs, even for finite $F$. An exponent $\tau\in\mathbb R$ is admissible if for every real $\varepsilon>0$ there is $C>0$ such that for every $N\ge1$ some formally correct program has cost at most $C N^{\tau+\varepsilon}$. Let $\omega_F(a,b,c)$ be the real infimum of the admissible exponents.

For every field $F$, the square exponent $\omega_F(1,1,1)$ is exactly $9/4$. The equality supplies both a lower and an upper bound.

## Depends on

- The formal polynomial interpretation and three rounded dimensions above.

## Proof depends on

- [Three-weight exact formula](formal-three-weight-rectangular-exponent.md), specialized at $(1,1,1)$; alternatively, matching square upper and lower bounds.

## Expansion

Once the formal exponent model and its sharp bounds are available, specialize and check the exact fraction $1+1+1/4$. Do not identify this equality with an asymptotic upper bound in the native point-evaluation model.

## Sources

- OpenAI, [MatrixExponent.lean, `FormalCorrect`, `formalOmega` and `square_exponent`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixExponent.lean#L86-L108).
