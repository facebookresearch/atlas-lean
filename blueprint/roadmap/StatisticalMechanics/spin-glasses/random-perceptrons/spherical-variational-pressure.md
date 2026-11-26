# The spherical perceptron variational pressure

Fix $\alpha,\beta>0$ and a bounded continuous $\phi:\mathbb R\to\mathbb R$. At size $N\ge1$ draw $\lfloor\alpha N\rfloor$ independent standard Gaussian rows $g_a\in\mathbb R^N$ and let $\sigma_N$ be sphere probability at radius $\sqrt N$. The random pressure is

$$
p_N=\frac1N\log\int\exp\left(\beta\sum_a\phi(g_a\cdot x/\sqrt N)\right)\,d\sigma_N(x).
$$

On continuous real paths on nonnegative times, let $P$ be any probability law under which the coordinate process $B$ is Brownian, with its completed right-continuous natural filtration. For a nondecreasing measurable $m:[0,1]\to[0,1]$, write $a_m(t)=\int_t^1m(s)\,ds$ and let the entropy be
$E(m)=\tfrac12\int_0^1(a_m(t)^{-1}-(1-t)^{-1})\,dt$, with extended nonnegative reciprocals, subtraction and integration. Let $V_m$ be the supremum over real progressive controls with $\mathbb E\int_0^1m v^2<\infty$ of

$$
\mathbb E\left[\beta\phi\!\left(B_1+\int_0^1m(t)v_t\,dt\right)\right]-\frac12\mathbb E\int_0^1m(t)v_t^2\,dt.
$$

The extended-real infimum $p=\inf_m(\alpha V_m+E(m))$ is a finite real number. The expectations of $p_N$ tend to $p$, and for every $\epsilon>0$ the Gaussian disorder probability of $|p_N-p|>\epsilon$ tends to zero. The source indexes all positive sizes as $N+1$.

**Conventions.** Use the native Gaussian row and spherical laws, Brownian progressive controls for the specified filtration, and the inverse-tail entropy integral. The trial functions include $m=0$, for which extended values must be handled rather than using real division by zero.

## Depends on

- [Monotone trial CDFs and reciprocal-tail entropy](reciprocal-trial-entropy.md)

## Proof depends on

Finite-cascade variational comparisons, a matching interpolation/reweighting argument, and disorder concentration for bounded single-pattern potential.

## Expansion

Prove Brownian control and entropy well-definedness, the matching pressure comparison, and the separate probability convergence. Establish the spherical normalization, then pass from finite hierarchy levels to the full monotone trial space without assuming smoothness of $\phi$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PerceptronFreeEnergy.lean#L97-L106)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/222.md)
- [Accompanying manuscript: The free energy of the spherical random perceptron](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-energy-of-the-spherical-random-perceptron-September-24-2026/The-free-energy-of-the-spherical-random-perceptron-September-24-2026.pdf)
