# Tensor restrictions and degenerations

An order-three tensor over a field $K$ with finite index sets $X,Y,Z$ is an array $T\in K^{X\times Y\times Z}$. $T$ is a *restriction* of $S\in K^{X'\times Y'\times Z'}$, written $T\le S$, if $T=(A\otimes B\otimes C)S$ for linear maps $A,B,C$. $T$ is a *degeneration of order $h$* of $S$ if there are maps over the polynomial ring $K[\varepsilon]$ with $(A(\varepsilon)\otimes B(\varepsilon)\otimes C(\varepsilon))S=\varepsilon^hT+\varepsilon^{h+1}E$ for some error tensor $E$. The *rank* $R(T)$ is the least $r$ with $T\le\langle r\rangle$ (the unit tensor), and the *border rank* $\underline R(T)$ the least $r$ such that $T$ is a degeneration of $\langle r\rangle$.

## Depends on

- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)
- [Trilinear tensors](../matrix-multiplication-exponent/trilinear-tensor.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
- Dario Bini, "Relations between exact and approximate bilinear algorithms. Applications", Calcolo, 1980.
