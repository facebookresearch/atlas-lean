# Distributional Kolmogorov complexity dK^t_λ(x|D) and its probabilistic variant

Let $U$ be an efficient universal machine and $U^t(d,y)$ its output on $(d,y)$ if it halts within $t$ steps (and $\bot$ otherwise). For $x\in\{0,1\}^*$, $t\in\mathbb{N}$, $\lambda\in(0,1]$ and a distribution $\mathcal D$ over $\{0,1\}^m$, the **$t$-time-bounded distributional Kolmogorov complexity** of $x$ given $\mathcal D$ is

$$
\mathrm{dK}^t_{\lambda}(x\mid\mathcal D)=\min\Bigl\{|d|:\ \Pr_{y\sim\mathcal D}\bigl[U^t(d,y)=x\bigr]\ge\lambda\Bigr\},
$$

and $\mathrm{dK}^{\tau}_\lambda(x\mid\mathcal D)=\mathrm{dK}^{\tau(n+m)}_\lambda(x\mid\mathcal D)$ for $n=|x|$. For a singleton distribution on $y$ it equals the conditional complexity $K^t(x\mid y)$. The oracle version $\mathrm{dK}^{\tau,A}$ uses an $A$-oracle universal machine, and the probabilistic version is $\mathrm{dpK}^t_\lambda(x\mid\mathcal D)=\min\{s:\Pr_{r\sim\{0,1\}^t}[\mathrm{dK}^t_\lambda(x\mid\mathcal D,r)\le s]\ge 3/4\}$. In the associated meta-computational problem the distribution is given as a circuit $D$ with $D(r)$, $r$ uniform, distributed as $\mathcal D$; approximating $\mathrm{dK}$ (with small additive error in $\lambda$) is in promise-$\mathsf{MA}$.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](../../kolmogorov-complexity/probabilistic-kolmogorov-and-symmetry-of-information/pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)

## Sources

- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
