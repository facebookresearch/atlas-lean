# Buffered Ising likelihood ratios for arbitrary boundary mixtures

Take a finite labelled edge list without loops and with nonnegative couplings $K_e$ (parallel edges are distinct), real site fields $h_v$, and pairwise-disjoint site sets $I,J,F$ with $i\in I$, $j\in J$. The Gibbs mass of a spin configuration $\sigma\in\{\pm1\}^V$ is proportional to $\exp(\sum_eK_e\sigma_{e_-}\sigma_{e_+}+\sum_vh_v\sigma_v)$. Fix assignments $a$ on $I$ and $\tau$ on $F$. For each assignment $b$ on $J$, let $p_b=P(\sigma_I=a\mid\sigma_J=b,\sigma_F=\tau)$. For two arbitrary probability weights $m,m'$ on boundary assignments, put $p_m=\sum_bm_b p_b$ and define $p_{m'}$ likewise.

Delete $F$ and its edges, contract the $I$ sites together and the $J$ sites together separately, and use the zero-field random-cluster law on retained edges. An open set $\omega$ has weight $2^{k(\omega)}\prod_{e\in\omega}(1-e^{-2K_e})\prod_{e\notin\omega}e^{-2K_e}$, with $k$ the number of components on that contracted graph including isolated vertices. Let $q_0$ be the probability that the two contracted terminals are connected. Then

$$
e^{-4\operatorname{artanh}q_0}\le p_m/p_{m'}\le e^{4\operatorname{artanh}q_0}.
$$

**Conventions.** Use finite Gibbs probabilities with arbitrary real fields and common pinned sites, and the zero-field $q=2$ random-cluster measure after deleting (not wiring) the common pins. Weights on full spin configurations give the same mixtures by pushing forward to their restrictions to $J$.

## Depends on

- [Pinned Ising conditionals and the contracted FK law](pinned-ising-fk-comparison-law.md)

## Expansion

A zero-field contracted-FK influence bound for arbitrary remaining fields, followed by a pointwise likelihood-ratio comparison and convex averaging over both mixtures.

Establish correspondence between the finite labelled-bond and native random-cluster model, including loops produced by contraction and summed parallel couplings. Prove all conditioning probabilities are positive and $q_0<1$ because the all-closed retained configuration has positive mass and the two terminals are distinct. Apply the comparison under fixed prescriptions before averaging; no weak-disorder continuum or stopping-band claim is included.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BufferedIsing.lean#L96-L110)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/218.md)
- [Accompanying manuscript: Buffered comparison and stopping-band resolution in critical Ising](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Buffered-comparison-and-stopping-band-resolution-in-critical-Ising-September-23-2026/paper.pdf)
