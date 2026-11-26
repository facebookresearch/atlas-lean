# Connected covers obstruct low-soundness agreement on high-dimensional expanders

Let $X$ be a $d$-dimensional complex and suppose $X$ has a connected $m$-sheeted cover $\rho : Y \to X$ with $m \ge 2$. Then for every $k$ there is an ensemble $\{f_s\}_{s \in X(k)}$ over the alphabet $\Sigma = [m] \times \{0,1\}$ that passes the $\sqrt{k}$-intersection agreement test on $X$ with probability at least $1/m$ while no global function $G : X(0) \to \Sigma$ agrees with $f_s$ on more than half of the coordinates for more than a $o(1)$-fraction of $s$ as $|X(0)| \to \infty$ (when $Y$ is an expander). Hence the low-acceptance agreement theorem fails on every complex with a small connected cover.

## Proof sketch

Choose an independent uniformly random function $g : Y(0) \to \{0,1\}$ and for each face $s$ of $X$ pick a uniformly random lift $\tilde{s} \subset Y$, setting $f_s = (\text{sheet}, g)|_{\tilde{s}}$. Two faces whose lifts lie in the same sheet over the intersection agree, which happens with probability $1/m$. Any global function would induce a section of the cover over most of $X$, impossible for a connected expanding cover.

## Depends on

- [Connected covers of a simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/covers-of-complexes.md)
- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)
- [Agreement tests for ensembles of local functions](agreement-test.md)

## Sources

- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
