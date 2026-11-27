# Plus-boundary Ising one-point function on a graph

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, $\beta \in \mathbb{R}$ and $x \in V$. The plus-boundary one-point function is

$$\langle s(\sigma_x) \rangle^+_\beta = \frac{1}{Z^+_\beta} \sum_\sigma w^+_\beta(\sigma)\, s(\sigma_x),$$

the sum over all two-state colorings $\sigma : V \to \{0, 1\}$, where $s(0) = 1$, $s(1) = -1$, $w^+_\beta$ is the [plus-boundary Ising weight](ising-wired-weight.md) and $Z^+_\beta$ the [plus-boundary partition function](ising-wired-z.md) (the quotient is read as $0$ if $Z^+_\beta = 0$).
