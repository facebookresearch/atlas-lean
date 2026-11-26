# Full support and diffusion identities for zero-temperature SK minimizers

Let $B$ be real Brownian motion on a probability space, with measurable time coordinates, and let $\gamma:[0,1)\to[0,\infty)$ be nondecreasing, right-continuous and Lebesgue integrable, extended by zero elsewhere. In the normalization $\xi(t)=t^2/2$, define $\Phi_\gamma(t,x)$ for $0\le t\le1$ as the supremum over progressively measurable controls $a$ bounded pointwise by one, using the natural filtration of the increments $B_{t+s}-B_t$, of

$$
\mathbb E\left[\left|x+B_1-B_t+\int_t^1\gamma(s)a_{s-t}\,ds\right|-\frac12\int_t^1\gamma(s)a_{s-t}^2\,ds\right].
$$

Assume $\gamma$ minimizes $\Phi_\gamma(0,0)-\tfrac12\int_0^1 t\gamma(t)\,dt$ over the stated class. There exists a Stieltjes measure on $[0,1)$ with $\mu([0,t])=\gamma(t)$, every such measure has full relative support, and $\gamma(a)<\gamma(b)$ whenever $0\le a<b<1$. There also exists a process progressive for the natural Brownian filtration, almost surely continuous on $[0,1]$, started at zero and satisfying $X_t=B_t+\int_0^t\gamma(s)\partial_x\Phi_\gamma(s,X_s)\,ds$ simultaneously there. For every such process and each $0\le t<1$,

$$
\mathbb E[(\partial_x\Phi_\gamma(t,X_t))^2]=t,\qquad
\mathbb E[(\partial_{xx}\Phi_\gamma(t,X_t))^2]=1.
$$

**Conventions.** Use the source's control value with terminal absolute value, shifted filtration for the controls, Brownian integral drift, and relative Stieltjes support. Derivatives evaluate the control value, not an arbitrary smooth surrogate.

State derivatives use the totalized derivative, which is zero at a point where differentiability fails.

## Depends on

- [Zero-temperature SK Brownian control value](../zero-temperature-sk-control-model.md)

## Proof depends on

Existence and regularity of the optimal-control value and its feedback diffusion, a no-gap first-variation argument, and the diffusion identities on the resulting full support.

## Expansion

Separate Stieltjes-measure existence from full support and strict increase. Prove diffusion existence and the feedback verification before drawing the two moment consequences for every solution. The minimizer is a premise; no existence theorem for minimizers is asserted.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKFullSupport.lean#L90-L93)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/281.md)
- [Accompanying manuscript: Full support of the zero-temperature Sherrington–Kirkpatrick order parameter](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf)
- [Background: Auffinger and Chen, Parisi formula for the ground state energy in the mixed p-spin model](https://arxiv.org/abs/1606.05335)
