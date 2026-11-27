# Constant-depth circuits cannot distinguish the Raz-Tal distribution from uniform

Every Boolean circuit of depth $d = O(1)$ and size $2^{\mathrm{polylog}(N)}$ on $2N$ inputs distinguishes $\mathcal{D}$ from the uniform distribution on $\{\pm 1\}^{2N}$ with advantage at most $\mathrm{polylog}(N)/\sqrt N$.

## Proof sketch

By Tal's bound, $L_{1,2}$ of every restriction of the circuit is at most $(c\log s)^{2(d-1)} = \mathrm{polylog}(N)$. The random walk lemma with $t = \mathrm{polylog}(N)$ and $\varepsilon = \Theta(1/\log N)$ bounds the advantage.

## Depends on

- [The Raz-Tal rounded Gaussian forrelation distribution](raz-tal-gaussian-forrelation-distribution.md)

## Proof depends on

- [Raz-Tal random walk lemma for multilinear functions on the cube](gaussian-random-walk-bound-for-multilinear-functions.md)
- [Tal's bound on level-l Fourier mass of constant-depth circuits](tal-level-l-fourier-bound-for-constant-depth-circuits.md)
- [Parity is not in AC0](../../circuit-complexity/lower-bounds-for-ac0-circuits/parity-not-in-ac0.md)

## Sources

- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), STOC (2019); ECCC TR18-107.
