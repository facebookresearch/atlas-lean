# Strassen's asymptotic spectrum of tensors and asymptotic rank

For tensors $S, T$ write $S \le T$ if $S$ is a restriction of $T$. The **asymptotic spectrum** $\Delta$ is the set of all maps $F$ from (isomorphism classes of) tensors to $\mathbb{R}_{\ge 0}$ that are monotone under restriction, multiplicative under $\otimes$, additive under $\oplus$ and normalized by $F(\langle 1 \rangle_r) = r$ for the unit tensor $\langle 1 \rangle_r = \sum_{i=1}^{r} x_iy_iz_i$. The **asymptotic rank** is $\underset{\sim}{R}(T) = \lim_N R(T^{\otimes N})^{1/N}$ and the **asymptotic subrank** is $\underset{\sim}{Q}(T) = \lim_N Q(T^{\otimes N})^{1/N}$, where $Q$ is the largest $r$ with $\langle 1 \rangle_r \le T$.

## Depends on

- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)

## Sources

- V. Strassen, "The asymptotic spectrum of tensors", Journal für die reine und angewandte Mathematik 384 (1988) 102-152.
- M. Christandl, P. Vrana, J. Zuiddam, "Universal points in the asymptotic spectrum of tensors", Journal of the American Mathematical Society 36 (2023); STOC (2018), arXiv:1709.07851.
