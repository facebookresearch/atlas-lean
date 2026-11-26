# State-dependent disturbance of a sequential measurement

Let $M^1,\dots,M^k$ be projective measurements, $\varphi$ a state, $i$ a coordinate, and $W_a$ contractions commuting with every effect of every $M^j$. Then

$$
\sum_g\operatorname{Re}\varphi(E_gW_{g_i})\le\sum_a\operatorname{Re}\varphi(M^i_aW_a)+2\sqrt{\delta_i},
$$

where $\delta_i$ is the prefix commutator defect at $i$. If questions $x_1,\dots,x_k$ are drawn independently and uniformly from a set $Q$, the measurements $M^x$ and their copies $R^y$ are projective with $M^x$ commuting with $R^y$, $\mathbb{E}_{x,y}$ pair defect$(M^x,M^y)\le\chi$ and $\mathbb{E}_x$ copy defect$(M^x,R^x)\le\zeta$, then $\mathbb{E}_x\delta_i\le(i-1)^2(2\chi+8\zeta)$ (counting coordinates from $1$).

## Proof sketch

Moving the target projector through each earlier product restores the isolated expression; the error is a sum of commutator terms, and Cauchy-Schwarz over the normalized family of transcript products bounds it by twice the square root of the prefix defect. For the average, the square root of the defect with a transcript is at most the sum over earlier factors of the root pair defect plus twice the root copy defect, since each factor can be replaced by its commuting copy; squaring the sum of $i-1$ terms and averaging gives the bound.

## Depends on

- [Sequential projective measurements and their commutator defects](sequential-projective-measurements.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
