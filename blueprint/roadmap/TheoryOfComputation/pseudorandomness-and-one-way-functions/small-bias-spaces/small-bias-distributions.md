# Bias, ε-biased and k-wise ε-biased distributions

Let $X$ be a probability distribution on $\{0,1\}^n$. For $S \subseteq [n]$ the *bias* of $X$ at $S$ is

$$
\mathrm{bias}_X(S) = \mathbb{E}_{x \sim X}\bigl[(-1)^{\bigoplus_{i \in S} x_i}\bigr] = \Pr\Bigl[\bigoplus_{i\in S} x_i = 0\Bigr] - \Pr\Bigl[\bigoplus_{i\in S} x_i = 1\Bigr],
$$

which equals $2^n$ times the Fourier–Walsh coefficient of the mass function of $X$ at $S$. The distribution is *$\varepsilon$-biased* if $|\mathrm{bias}_X(S)| \le \varepsilon$ for every nonempty $S$, and *$k$-wise $\varepsilon$-biased* if this holds for every nonempty $S$ with $|S| \le k$. A sample space $G : \sigma \to \{0,1\}^n$ (a generator with seed set $\sigma$) is $\varepsilon$-biased if the image of the uniform seed is. The uniform distribution is $0$-biased.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Fourier–Walsh coefficient under the uniform measure](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-fourier-coeff.md)
- [Uniform distribution on a finite type](../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing, 1993.
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms, 1992.
