# Decay and entropy parameters for thin products

For naturals $L\ge10m$ and $t\le m$, put $D=4^m$, $K=\binom Lm$, $N_0=3^{L-m}$, $\rho=9m/(L-m+1)$, and $\alpha_d=\binom md9^d$. For reals $c>10$ and $0<\theta<0.9$, put $\rho_c=9/(c-1)$, $\gamma=\theta\log(1/\rho_c)/\log4$, $q=(H(\theta)+\theta\log9)/\log4$, where $H(x)=-x\log x-(1-x)\log(1-x)$. Set

$$
R_c(g)=\frac{\log 4}{c\log 10-\frac12 cH(1/c)-(c-1)\log3+g\log4},\qquad \varepsilon_*=\frac{\log4}{5\log10}.
$$

All logarithms here are natural.

## Expansion

Separate the decay, entropy and parameter-choice estimates from proving the algorithm; retain strict inequalities in selecting parameters.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [the parameter definitions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L1973-L2032).
