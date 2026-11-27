# k-wise independent and almost k-wise independent distributions

A distribution $\nu$ on $\{0,1\}^n$ is *$k$-wise independent* if its marginal on every set of at most $k$ coordinates is uniform; equivalently, all Fourier biases $\mathbb{E}_{x\sim\nu}[(-1)^{\sum_{i\in S}x_i}]$ vanish for $1\le|S|\le k$. It is *$\varepsilon$-almost $k$-wise independent* if every such marginal is within statistical distance $\varepsilon$ of uniform. A distribution $\nu$ *$\varepsilon$-fools* a function $f$ if $|\mathbb{E}_\nu f-\mathbb{E}_U f|\le\varepsilon$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM 57(5), Article 28, 2010.
- Noga Alon, Oded Goldreich, Johan Håstad, René Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 1992.
