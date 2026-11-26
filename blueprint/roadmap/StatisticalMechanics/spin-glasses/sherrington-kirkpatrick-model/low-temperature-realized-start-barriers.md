# Low-temperature SK obstructions from Gibbs-distributed starts

Fix $\beta>1$. On $\{-1,1\}^n$ give spin $x$ Gibbs mass proportional to $\exp(\beta n^{-1/2}\sum_{i<j}J_{ij}x_ix_j)$, with independent standard real Gaussian $J_{ij}$. The discrete kernel chooses a uniform site and resamples from its Gibbs conditional law. The continuous kernel at $t$ is the mixture of $k$-attempt kernels with Poisson weights of mean $nt$ (rate one per site). Both allow holding. Put $T_n=\exp(n^{1/10000})$.

The expected Gibbs mass of starts whose continuous-time law at $T_n$ is more than $1/4$ from Gibbs in total variation tends to one over the Gaussian disorder. The expected Gibbs mass of starts whose law after $\lfloor T_n\rfloor$ discrete attempts is more than $1/4$ away also tends to one. These are claims about the statewise distance before averaging over the initial state; a chain initialized with the whole Gibbs distribution is stationary.

**Conventions.** Use the zero-field Gaussian SK Hamiltonian, the one-site conditional probability $e^{\beta s h_i}/(2\cosh(\beta h_i))$ for spin $s$ at local normalized field $h_i$, and Poissonization of the discrete kernel.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

Low-temperature free-energy/barrier estimates giving slow transitions from Gibbs-typical individual starts, and enough quantitative control on the Poisson time-change at $T_n$.

## Expansion

Bridge the rescaled standard-normal coupling to the native SK normalization. Prove finite-time escape control, then integrate the mass of bad starts over disorder. Keep $T_n$ and the natural floor in the two conclusions distinct; no exact exponential rate in $n$ is claimed.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKBarriers.lean#L84-L88)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Stretched-exponential barriers for typical SK initial states](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf)
