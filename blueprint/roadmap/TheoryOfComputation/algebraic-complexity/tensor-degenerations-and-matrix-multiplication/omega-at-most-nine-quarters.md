# The matrix multiplication exponent is at most 9/4

Over every field of characteristic zero, for every $\gamma>0$, $n\times n$ matrix multiplication has arithmetic circuits of size $O(n^{9/4+\gamma})$. Hence $\omega\le 9/4$.

## Proof sketch

A product of a canonical polynomial-multiplication tensor with its two role exchanges contains every leg permutation of $\mathrm{Full}_{a,b}$ equally often, restricts to matrix multiplication at $a=b=1$, and has rank at most $(a+b-1)^{6d}$. Column packings built from the primal packing degenerate many copies into fewer ones; iterating and converting degenerations to exact algorithms yields, for some $v$, an exact bilinear algorithm for $v\times v$ multiplication with fewer than $v^{\tau}$ multiplications for every $\tau>9/4$, which Strassen's block recursion turns into the circuit bound.

## Depends on

- [Matrix multiplication exponent](../matrix-multiplication-exponent/matrix-multiplication-exponent.md)
- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)
- [Tensor restrictions and degenerations](tensor-restrictions-and-degenerations.md)

## Proof depends on

- [Pass's primal packing of polynomial products](primal-packing-of-polynomial-products.md)
- [Bini's theorem: border rank bounds the matrix multiplication exponent](bini-border-rank-bounds-omega.md)
- [Strassen: arithmetic circuits for matrix multiplication yield bilinear algorithms](strassen-bilinear-rank-from-circuits.md)

## Sources

- Rafael Pass, "Matrix Multiplication from Polynomial Packings: A Constructive and Elementary Proof of ω ≤ 9/4", arXiv:2610.28627, 2026.
- OpenAI, "An Upper Bound of 9/4 for the Matrix Multiplication Exponent", preprint, 2 October 2026.
