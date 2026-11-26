# Critical SK obstruction for realized equilibrium starting states

At size $n$, let $W_{ij}$ for $i<j$ be independent $N(0,1/n)$ couplings. The zero-field critical Gibbs law $\pi_W$ on $\{-1,1\}^n$ gives each $x$ mass proportional to $\exp(\sum_{i<j}W_{ij}x_ix_j)$. Given $W$, $P_i$ resamples spin $i$ from its Gibbs conditional distribution given all other spins, including the option of leaving it unchanged. At positive $n$ the discrete transition is $P=n^{-1}\sum_i P_i$, and the continuous generator is $L=\sum_i(P_i-I)$. For fixed $x$ write $d_c(W,t,x)=\|e^{tL}(x,\cdot)-\pi_W\|_{\rm TV}$ and $d_d(W,k,x)=\|P^k(x,\cdot)-\pi_W\|_{\rm TV}$.

If a deterministic sequence $t_n\ge0$ has $t_n/n^{2/3}\to0$, the random variable $\pi_W\{x:d_c(W,t_n,x)>1/4\}$ tends to one in disorder probability. For any deterministic natural $k_n$ with $k_n/n^{5/3}\to0$, $\pi_W\{x:d_d(W,k_n,x)>1/4\}$ likewise tends to one in disorder probability. In each case the probability of absolute deviation from one at least any fixed $\delta>0$ tends to zero. The distance is from each realized start, not from the already stationary mixture.

**Conventions.** Use the SK Hamiltonian on unordered pairs, the Gibbs heat-bath kernel and its rate-one-per-site generator, and total variation as half the sum of atom differences.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

Critical equilibrium fluctuation estimates producing slow linear observables, and dynamical bounds that turn their slow change into a typical-start obstruction rather than just a worst-start one.

## Expansion

Prove the compatibility between the edge-array Gibbs law and the native SK model, then construct the continuous and discrete transitions for that Gibbs law. Isolate the conditional-disorder slow-observable argument and extract both time scales without taking worst-start or annealed state-space distances in place of the realized-start distances.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSK.lean#L110-L124)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Critical slowing down in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf)
