# The first derived limit of a tower

Let $R$ be a ring and $(B_n, d_n)_{n \in \mathbb{N}}$ an inverse system of $R$-modules indexed by $\mathbb{N}$, with
transition maps $d_n \colon B_{n+1} \to B_n$. Its first derived limit is the cokernel

$$
\varprojlim\nolimits^1_n B_n = \operatorname{coker}\Bigl(\prod_n B_n \xrightarrow{\ \mathrm{id} - d\ } \prod_n B_n\Bigr),
\qquad (b_n)_n \longmapsto (b_n - d_n(b_{n+1}))_n,
$$

whose kernel is $\varprojlim_n B_n$. Neukirch–Schmidt–Wingberg define $\varprojlim^p$ as the right derived functors
of $\varprojlim$ on inverse systems indexed by $\mathbb{N}$ and show, for $R$-modules, that
$\varprojlim^p = 0$ for $p \ge 2$ and that $\varprojlim^1$ is this cokernel, through the canonical exact sequence
$0 \to \varprojlim_n B_n \to \prod_n B_n \to \prod_n B_n \to \varprojlim^1_n B_n \to 0$.

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, inverse systems indexed by
  $\mathbb{N}$ and the derived functors of $\varprojlim$, p. 138, and Proposition (2.7.4), p. 139.
