# The inner product needs n multiplications

Over every field (including characteristic two), every arithmetic circuit computing the bilinear form $\sum_{i=1}^nx_iy_i$ as a formal polynomial uses at least $n$ multiplication gates, even with arbitrary constants, negative coefficients and cancellation.

## Proof sketch

The Hessian of $\sum x_iy_i$ is the block-swap matrix $\begin{pmatrix}0&I\\I&0\end{pmatrix}$ of rank $2n$; by the Hessian rank bound, $2n\le2\mu$.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Hessian rank bounds the number of multiplications](hessian-rank-bounds-multiplications.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
