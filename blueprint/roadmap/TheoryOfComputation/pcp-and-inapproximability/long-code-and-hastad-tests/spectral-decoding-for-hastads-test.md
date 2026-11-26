# Spectral decoding: Håstad's test against Label Cover

Let $\varepsilon > 0$ and $\delta \in (0, 1/2)$. There is $\eta = \eta(\varepsilon, \delta) > 0$ such that for every Label Cover instance and every assignment of folded tables to its vertices, if Håstad's test applied to a uniformly random edge accepts with probability at least $1/2 + \varepsilon$, then the instance has a labelling satisfying at least an $\eta$ fraction of its edges. Moreover the labelling can be taken randomized: choose $T$ with probability $\hat B_w(T)^2$ (restricted to $|T| \le k(\varepsilon, \delta)$) and a uniform element of $T$, and dually for the left tables.

## Proof sketch

By the Fourier formula, an acceptance advantage $\varepsilon$ on average over edges forces $\mathbb{E}_e \sum_T (1-2\delta)^{|T|} \hat B(T)^2 |\hat A(\pi_2(T))| \ge 2\varepsilon$. The noise damps large sets, so sets of size at most $k$ carry the mass; Cauchy–Schwarz and Parseval show the random decoding satisfies an edge with probability $\Omega(\varepsilon^2/k)$, using that folded tables have $\hat A(\emptyset) = 0$ so $\pi_2(T)$ is nonempty.

## Depends on

- [Håstad's noisy 3-bit linear test on a projection](hastad-noisy-three-bit-linear-test.md)
- [Label Cover (projection games)](../two-prover-games-and-parallel-repetition/label-cover-projection-games.md)

## Proof depends on

- [Fourier expansion and completeness of Håstad's 3-bit test](fourier-expansion-of-hastads-test.md)
- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
