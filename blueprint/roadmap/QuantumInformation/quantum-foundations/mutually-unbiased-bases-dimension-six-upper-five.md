# At most five mutually unbiased bases in dimension six

Let $(B_r)_{r=1}^n$ be a family of orthonormal bases of $\mathbb C^6$, each indexed by six vectors. Assume that for every distinct $r,s$ and every pair of vectors $u\in B_r$, $v\in B_s$, the squared modulus of the Hermitian inner product is $1/6$. Then $n\leq5$. The statement does not exclude four bases and makes no assertion about existence of a five-basis family.

## Depends on
Orthonormal bases in complex Euclidean dimension six and squared, rather than unsquared, unbiasedness between distinct bases.

## Proof depends on

- [Order-six Hadamard Fourier vanishing](../../LinearAlgebra/special-matrices/order-six-hadamard-fourier-vanishing.md).

The completion of any six mutually unbiased bases to seven, and a seven-basis obstruction that uses simultaneous transition-matrix vanishing and the mixed Gram certificate.

## Expansion

Normalize one basis and handle the exceptional Tao equivalence before applying Fourier constraints to every required transition matrix. Justify the seven-basis mixed Gram obstruction and separately formalize the six-to-seven completion preserving the original bases. Restrict larger candidate families to six before using nonexistence.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MUBSix.lean#L56-L61) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/266.md).
