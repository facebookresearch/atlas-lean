# One-way puzzles

A *one-way puzzle* is a pair of algorithms: a quantum polynomial-time sampler $\mathsf{Samp}(1^\lambda)\to(s,k)$ outputting a classical puzzle $s$ and a classical key $k$, and an (inefficient) verification predicate $\mathsf{Ver}(s,k')\in\{0,1\}$, such that $\mathsf{Ver}(s,k)=1$ with overwhelming probability for honestly sampled pairs, while every quantum polynomial-time adversary given $s$ outputs $k'$ with $\mathsf{Ver}(s,k')=1$ with negligible probability. One-way puzzles are a classical-output quantum relaxation of one-way functions in which the sampler is quantum.

## Sources

- Dakshita Khurana, Kabir Tomer, "Commitments from Quantum One-Wayness", STOC (2024), arXiv:2310.11526.
