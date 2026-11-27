# Strassen: arithmetic circuits for matrix multiplication yield bilinear algorithms

Over every field $K$, if a division-free arithmetic circuit computes the $n^2$ entries of the product of two generic $n\times n$ matrices with $\mu$ multiplication gates whose two inputs are both non-constant (in particular with at most $\mu$ gates), then the tensor rank of $\langle n,n,n\rangle$ is at most $2\mu$. (With divisions the same bound holds over infinite fields, by Strassen's division elimination.)

## Proof sketch

Take bihomogeneous components: for a product gate $w=uv$, the bidegree-$(1,1)$ part of $w$ is $u_{A}v_{B}+u_{B}v_{A}$ plus constant multiples of the bidegree-$(1,1)$ parts of $u$ and $v$, where $u_A,u_B$ are the linear parts of $u$ in the entries of $A$ and of $B$. By induction every gate's bidegree-$(1,1)$ part is a linear combination of the at most $2\mu$ products $u_Av_B$ and $u_Bv_A$, and the outputs are bilinear, giving a bilinear algorithm of rank at most $2\mu$.

## Depends on

- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)
- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)
- [Square matrix multiplication circuit exponent](../arithmetic-circuits-for-matrix-multiplication/square-matrix-multiplication-circuit-exp.md)

## Sources

- Volker Strassen, "Vermeidung von Divisionen", Journal für die reine und angewandte Mathematik, 1973.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
