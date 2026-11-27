# Zero-temperature SK value identities and finite Gaussian approximants

Let $\gamma$ and the Brownian control value $\Phi_\gamma$ be as in the [zero-temperature SK functional](../zero-temperature-sk-control-model.md), now writing $\gamma$ as a real function nonnegative, monotone and right-continuous on $[0,1)$ and integrable on $(0,1]$, and freezing a Brownian probability space with strongly measurable time coordinates. First assume $\gamma$ minimizes the Parisi functional and there is an adapted $X$ (stopped at time $1$ for the adaptation condition), almost surely continuous on $[0,1]$ and satisfying $X_t=B_t+\int_0^t\gamma(s)\partial_x\Phi_\gamma(s,X_s)\,ds$ there. Let $E_n=n^{-1}\mathbb E\max_x n^{-1/2}\sum_{i<j}J_{ij}x_ix_j$ over spins $\pm1$ and independent standard Gaussian $J_{ij}$, and let $E_*$ be its real filter-limit. Then $E_n\to E_*$ and there exists $U$ with $|U|\le1$, $U^2=1$ almost surely, such that $m_t=\partial_x\Phi_\gamma(t,X_t)$ for $t<1$, stopped at $U$ for $t\ge1$, is a martingale and $m_t\to U$ almost surely and in $L^2$ as $t\uparrow1$. The curvature expectation is interval-integrable and

$$
E_*=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt=\mathbb E[UB_1]=\int_0^1\mathbb E[\partial_{xx}\Phi_\gamma(t,X_t)]\,dt.
$$

For each $0<T<1$ and the same minimizer and diffusion premises, let $\Delta=T/N$, $t_j=j\Delta$, and use $N+1$ independent standard Gaussian scalars $Z_0,\ldots,Z_N$. Start $Y_0=0$ and iterate $Y_{j+1}=Y_j+\sqrt\Delta Z_j+\Delta\gamma(t_j)\partial_x\Phi_\gamma(t_j,Y_j)$ through $j=N-1$. Put $R_j=\partial_{xx}\Phi_\gamma(t_j,Y_j)$, $a_j=(\mathbb E R_j^2)^{-1/2}$, and $L=\operatorname{sign}(\partial_x\Phi_\gamma(T,Y_N)+2\mathcal N(Z_N)-1)$ with $\mathcal N$ the standard Gaussian CDF. Eventually every $a_j>0$ for $j<N$; the sum $\sum_{j=0}^{N-1}\mathbb E[L a_jR_jZ_j]\,\mathbb E[L Z_{j+1}]$ tends to $\int_0^T\mathbb E[\partial_{xx}\Phi_\gamma(t,X_t)]\,dt$. That integral tends to $E_*$ as $T\uparrow1$. With the source indexing this is $\sum_{j=0}^{N} A_j B_{j+1}$: $A_0=0$, $A_j$ for $j>0$ uses step $j-1$, and $B_i$ uses Gaussian coordinate $i-1$.

With the minimizer premise alone the final clause is $E_*=\Phi_\gamma(0,0)-\tfrac12\int_0^1 t\gamma(t)\,dt$. There is no assertion about a sequence of quantum circuit energies.

The source normalization of the Gaussian ground-state sequence and the control functional, its derivatives, and the adapted diffusion; the Gaussian Euler scheme uses a separate independent rounding coordinate.

The state derivatives are totalized to zero at nondifferentiability, and $\operatorname{sign}(0)=0$. No unshifted coefficient limit is asserted.

## Depends on

- [Zero-temperature SK Brownian control value](../zero-temperature-sk-control-model.md)

## Proof depends on

A zero-temperature variational identification for the finite-system ground states, martingale and terminal estimates for the gradient process, and convergence of the Euler approximants and the shifted Gaussian coefficient sum.

## Expansion

Separate the scalar identities from the fixed-terminal-time Gaussian limit and the endpoint passage $T\uparrow1$. Prove nonvanishing of each raw curvature normalizer before division. Preserve the explicit indexing of both finite coefficients, and keep the last minimizer-only value identity logically distinct from the diffusion-conditional identities.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKValue.lean#L163-L172)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/281.md)
- [Accompanying manuscript: QAOA attains the SK ground-state energy in the thermodynamic-first limit](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf)
