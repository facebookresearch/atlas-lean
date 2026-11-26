# Exact learning of degree-k Boolean functions from $2 \cdot 4^k \ln(2N/\delta)$ uniform examples

Let $k \ge 1$ and let $C$ be the Boolean functions on $n$ coordinates whose sign representation has Fourier degree at most $k$. Let $N = |\{S : |S| \le k\}| \le (n+1)^k$. Estimating every $\hat f(S)$ with $|S| \le k$ from $m \ge 2\cdot 4^k\ln(2N/\delta)$ uniform random examples and rounding each estimate to the nearest multiple of $2^{1-k}$ recovers all coefficients exactly with probability at least $1 - \delta$; the resulting hypothesis equals $f$, i.e. $C$ is learned with error $0$ and confidence $1 - \delta$, using $O(4^k(k\log(n+1) + \log(1/\delta)))$ examples.

## Proof sketch

A Boolean function of degree at most $k$ has all Fourier coefficients in $2^{1-k}\mathbb{Z}$ (granularity). By Hoeffding and a union bound, every estimate is within $2^{-k}$ of the true coefficient with probability at least $1-\delta$, and then rounding is exact; Fourier inversion recovers $f$.

## Depends on

- [Learning from uniform random examples](learning-from-uniform-random-examples.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
