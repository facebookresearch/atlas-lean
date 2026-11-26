# GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution

$\mathrm{GapMCSP}[s,c]$ is the promise problem of distinguishing truth tables of length $N$ whose circuit complexity is at most $s$ from those whose circuit complexity is at least $c$; $\mathrm{GapK}[s,c]$ distinguishes strings with (time-unbounded) Kolmogorov complexity at most $s$ from those with complexity at least $c$; and for a time bound $\tau$, $\mathrm{GapK}^{\tau}[s,c]$ uses $K^{\tau}$, the $\tau$-time-bounded complexity. A promise problem $\Pi$ is **weakly average-case hard** on a distribution family $\mathcal D$ if every probabilistic polynomial-time algorithm fails to solve $\Pi$ (on promise inputs) with probability at least $1/n^{O(1)}$ over $\mathcal D_n$ and its coins, on almost all input lengths $n$; it is **strongly average-case hard** if every such algorithm fails with probability at least $1/2-1/n^{\omega(1)}$ on almost all input lengths.

## Depends on

- [Locally samplable distributions on truth tables](locally-samplable-distributions.md)
- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
