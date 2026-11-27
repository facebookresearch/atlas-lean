# Bini's theorem: border rank bounds the matrix multiplication exponent

If, for some $n\ge2$, the matrix multiplication tensor $\langle n,n,n\rangle$ has border rank at most $r$ over a field $K$, then $\omega_K\le\log_nr$. More generally degenerations compose: if $T$ is a degeneration of order $h$ of $S$ and $S$ of order $h'$ of $U$, then $T$ is a degeneration of order $h+h'$ of $U$; and if $T$ is a degeneration of order $h$ of $\langle r\rangle$ then $R(T)\le\binom{h+2}{2}r$, so if $T$ is a degeneration of order $h$ of $\langle\underline R(T)\rangle$, then $R(T^{\otimes k})\le\binom{hk+2}{2}\,\underline R(T)^k$.

## Proof sketch

Interpolation in $\varepsilon$: the coefficient of $\varepsilon^h$ in a degeneration is a linear combination of $h+1$ evaluations (or of coefficient extractions), turning an approximate algorithm into an exact one with polynomial overhead in $h$; tensor powers keep $h$ linear in $k$, so the overhead vanishes in the exponent.

## Depends on

- [Tensor restrictions and degenerations](tensor-restrictions-and-degenerations.md)
- [Matrix multiplication exponent](../matrix-multiplication-exponent/matrix-multiplication-exponent.md)
- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)

## Sources

- Dario Bini, "Relations between exact and approximate bilinear algorithms. Applications", Calcolo, 1980.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
