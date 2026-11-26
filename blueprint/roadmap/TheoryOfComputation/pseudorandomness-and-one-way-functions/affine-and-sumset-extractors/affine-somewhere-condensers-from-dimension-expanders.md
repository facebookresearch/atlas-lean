# Li–Zhong linear affine somewhere condensers from dimension expanders

A map $C : \mathbb{F}_2^{n} \to (\mathbb{F}_2^{n'})^D$ is a *$(\delta, \gamma)$ affine somewhere condenser* if for every affine source $X$ of rate at least $\delta$ some output $C(X)_j$ is an affine source of rate at least $\gamma$. Linear maps $T_1, \dots, T_d$ on $\mathbb{F}_2^{m}$ form an *$\alpha$-dimension expander* if $\dim(V + \sum_i T_i V) \ge (1 + \alpha)\dim V$ for every subspace $V$ of dimension at most $m/2$. The basic condenser sends $(x_1, x_2)$ to the tuple $(x_1, x_2, x_1 + T_1x_2, x_2 + T_1x_1, \dots, x_1 + T_dx_2, x_2 + T_dx_1)$. For $0 < \delta \le 1/2$, $d \ge 3$ and $0 < \alpha \le 1$, it is a $(\delta, (1 + \alpha/(4d))\delta)$ affine somewhere condenser, and iterating it $h + 1$ times with $1/2 \le \delta(1 + \alpha/(4d))^h$ condenses every rate $\delta \in (0, 1/2]$ to rate $1/2 + \alpha/(8d)$.

## Proof sketch

Split the direction of $X$ into its projections on the two halves. If neither half already has higher rate, the expander property applied to the smaller projection forces some output $x_1 + T_ix_2$ or $x_2 + T_ix_1$ to have dimension larger by a factor $1 + \alpha/(4d)$. Induct on the number of halving rounds.

## Depends on

- [Affine sources, affine extractors and sumset extractors](affine-sources-and-sumset-extractors.md)

## Sources

- X. Li and Y. Zhong, "Explicit Directional Affine Extractors and Improved Hardness for Linear Branching Programs", 39th Computational Complexity Conference (CCC 2024), 2024.
