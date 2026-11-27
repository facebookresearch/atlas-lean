# Compressing samples of a polynomial-time computable ensemble

For every polynomial-time computable ensemble $\mathcal{D}$ there is a polynomial-time code $C$, injective on the words of each length, with $|C(x)|\le\min\bigl(|x|+1,\ 1+\log_2(1/D_n(x))\bigr)$, i.e. $2^{|C(x)|}D_n(x)\le2$. This is the key step of Levin's theorem that the bounded halting problem under the uniform-type distribution is complete for $\mathsf{DistNP}$.

## Proof sketch

If $D_n(x)\le2^{-|x|}$, let $C(x)=0x$. Otherwise let $C(x)=1z$ where $z$ is the longest common prefix of the binary expansions of $F(x^-)$ and $F(x)$, which has length at most $\log_2(1/D_n(x))$ and is computable since $F$ is; intervals of distinct $x$ are disjoint, giving injectivity.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](../distributional-problems.md)

## Sources

- Andrej Bogdanov and Luca Trevisan, "Average-Case Complexity", Foundations and Trends in Theoretical Computer Science 2(1), arXiv:cs/0606037, 2006, Claim 20.
- Leonid A. Levin, "Average Case Complete Problems", SIAM Journal on Computing 15(1), 1986.
