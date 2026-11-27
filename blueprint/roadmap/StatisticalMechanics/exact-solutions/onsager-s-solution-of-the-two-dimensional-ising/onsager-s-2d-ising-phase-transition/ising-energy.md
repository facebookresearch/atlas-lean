# Energy of an Ising configuration

For $L \ge 1$ and $\sigma : (\mathbb{Z}/L\mathbb{Z})^2 \to \{0, 1\}$, with spins $s_p = +1$ if $\sigma(p) = 1$ and $s_p = -1$ otherwise, the energy is

$$H_L(\sigma) = -\sum_{p} \big(s_p\, s_{p + (1,0)} + s_p\, s_{p + (0,1)}\big),$$

the sum running over all sites $p$ of the torus (for $L = 1$ and $L = 2$ the neighbours wrap around, so some bonds are counted with multiplicity).
