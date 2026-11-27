# Critical SK covariance norm and linear inverse-Rayleigh scale

Use the [critical Gibbs law and rate-one heat bath](gaussian-sk-heat-bath.md) at $\beta=1$ with independent off-diagonal couplings of variance $1/n$. Let $C_W=(\operatorname{Cov}_{\pi_W}(X_i,X_j))_{i,j}$ act on Euclidean space, and put

$$
R_W=\sup_{a\ne0}\frac{\operatorname{Var}_{\pi_W}(\sum_i a_i X_i)}{\sum_i\mathbb E_{\pi_W}[(f_a-P_i f_a)^2]},\qquad f_a(x)=\sum_i a_i x_i.
$$

For every deterministic sequence $M_n>0$ with $M_n\to\infty$, the joint disorder probability that both $\|C_W\|_{2\to2}$ and $R_W$ belong to $[n^{2/3}/M_n,M_n n^{2/3}]$ tends to one. The supremum is over linear spin tests only, not over arbitrary observables.

**Conventions.** Use the real Euclidean operator norm and the unscaled sum of site conditional variances.

The real supremum uses the native totalization on an empty or unbounded set.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

Matching critical susceptibility matrix estimates and heat-bath activity comparisons on the linear test subspace.

## Expansion

Prove measurability of the norm and Rayleigh random variables, and positivity of the Dirichlet denominator on nonzero tests for $n>0$. Separate the covariance scaling from the comparison to this restricted Rayleigh supremum. No upper bound on the full inverse spectral gap follows from the restriction alone.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSK.lean#L125-L135)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Critical slowing down in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf)
