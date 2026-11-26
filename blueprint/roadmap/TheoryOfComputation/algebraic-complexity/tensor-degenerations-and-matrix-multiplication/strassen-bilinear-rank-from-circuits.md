# Strassen: arithmetic circuits for matrix multiplication yield bilinear algorithms

Over an infinite integral domain $K$, if an arithmetic circuit computes $n\times n$ matrix multiplication with $\mu$ multiplication gates (in particular with at most $\mu$ gates), then the tensor rank of $\langle n,n,n\rangle$ is at most $2\mu$.

## Proof sketch

Homogenize: the bilinear part (bidegree $(1,1)$ component) of each product gate's inputs gives, for each multiplication, at most two bilinear products $(\ell_A\cdot\ell'_B)$ and $(\ell'_A\cdot\ell_B)$ of a linear form in the entries of $A$ and one in the entries of $B$; the output's bilinear component is a linear combination of these, a bilinear algorithm of rank at most $2\mu$.

## Depends on

- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)
- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)
- [Square matrix multiplication circuit exponent](../arithmetic-circuits-for-matrix-multiplication/square-matrix-multiplication-circuit-exp.md)

## Sources

- Volker Strassen, "Vermeidung von Divisionen", Journal für die reine und angewandte Mathematik, 1973.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
