# One quantum query distinguishes the Raz-Tal distribution from uniform

There is a quantum algorithm making one query to $z \in \{\pm1\}^{2N}$ (interpreted as truth tables of $f$ and $g$) and running in time $O(\log N)$ whose acceptance probabilities on $z \sim \mathcal{D}$ and on uniform $z$ differ by $\Omega(\varepsilon) = \Omega(1/\log N)$.

## Proof sketch

Run the forrelation algorithm. Under the uniform distribution $\mathbb{E}[\Phi] = 0$. Under $\mathcal{D}$, $\mathbb{E}[\Phi(z)] = N^{-1}\sum_{i,j} (H_N)_{ij}\, \mathbb{E}[Z_{X,i} Z_{Y,j}]$, and since clipping occurs with probability $N^{-\Omega(1)}$ at variance $\varepsilon$, this is $\varepsilon\, N^{-1}\mathrm{Tr}(H_N^2) - o(\varepsilon) = \Omega(\varepsilon)$.

## Depends on

- [The Raz-Tal rounded Gaussian forrelation distribution](raz-tal-gaussian-forrelation-distribution.md)

## Proof depends on

- [A one-query quantum algorithm estimating forrelation](one-query-quantum-algorithm-for-forrelation.md)

## Sources

- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), STOC (2019); ECCC TR18-107.
