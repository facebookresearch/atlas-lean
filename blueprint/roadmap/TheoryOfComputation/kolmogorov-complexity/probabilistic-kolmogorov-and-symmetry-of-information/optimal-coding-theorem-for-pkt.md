# Lu–Oliveira–Zimand: an optimal coding theorem for pK^t over polynomial-time samplable distributions

For every polynomial-time samplable distribution family $\{D_n\}_{n\in\mathbb{N}}$ (each $D_n$ supported on $\{0,1\}^n$) there is a polynomial $p$ such that for all $n$ and all $x$ in the support of $D_n$,

$$
\mathrm{pK}^{p(n)}(x)\ \le\ \log\frac{1}{D_n(x)}+O(\log n).
$$

This matches the classical coding theorem $K(x)\le\log(1/D(x))+O(1)$ for computable measures up to the additive $O(\log n)$ term, and it holds unconditionally. By contrast, for $\mathrm{rKt}$, the randomized (private-coin) analogue of Levin's $\mathrm{Kt}$, which charges program length plus the logarithm of the running time, Lu, Oliveira and Zimand prove an efficient coding theorem $\mathrm{rKt}(x)\le(2+o(1))\log(1/D_n(x))+O(\log n)$, and show that, under a hypothesis on the security of cryptographic pseudorandom generators, no efficient coding theorem can achieve $\mathrm{rKt}(x)\le(2-o(1))\log(1/D_n(x))+\mathrm{poly}(\log n)$.

## Proof sketch

Write $\delta=D_n(x)$; the strings of probability at least $\delta/2$ form a set of size at most $2/\delta$. The public random string $w$ supplies the shared randomness that both the encoder and the time-bounded decoder need: it fixes a hash function isolating $x$ inside this heavy set and the randomness for an efficient reconstruction procedure, so a description of length $\log(1/\delta)+O(\log n)$ suffices for most $w$. Because the description length is measured relative to a fixed public $w$, the conditional factor-$2$ barrier for efficient coding theorems for the private-randomness measure $\mathrm{rKt}$ does not arise.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [The universal time-bounded sampler hits every x with probability about 2^{−pK^t(x|y)}](universal-time-bounded-sampler-and-pkt.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Zhenjian Lu, Igor C. Oliveira and Marius Zimand, "Optimal Coding Theorems in Time-Bounded Kolmogorov Complexity", ICALP (2022).
