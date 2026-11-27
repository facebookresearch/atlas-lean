# Small-bias distribution and generator

A distribution $D$ on $\{0,1\}^\ell$ is *$\varepsilon$-biased* if for every nonempty set $S \subseteq \{1, \dots, \ell\}$,

$$\mathrm{bias}_S(D) = \Bigl|\Pr_{y \leftarrow D}\Bigl[\bigoplus_{i \in S} y_i = 0\Bigr] - \Pr_{y \leftarrow D}\Bigl[\bigoplus_{i \in S} y_i = 1\Bigr]\Bigr| \le \varepsilon.$$

A generator is an *$\varepsilon$-bias generator* if its output on a uniform seed is $\varepsilon$-biased. The uniform distribution is $0$-biased, and an $\varepsilon$-biased distribution fools every parity test with advantage $\varepsilon/2$.

More generally, for a distribution $X$ on $\{0,1\}^n$ and $S \subseteq [n]$ the *signed bias* of $X$ at $S$ is

$$
\mathrm{bias}_X(S) = \mathbb{E}_{x \sim X}\bigl[(-1)^{\bigoplus_{i \in S} x_i}\bigr] = \Pr\Bigl[\bigoplus_{i\in S} x_i = 0\Bigr] - \Pr\Bigl[\bigoplus_{i\in S} x_i = 1\Bigr],
$$

which equals $2^n$ times the Fourier–Walsh coefficient of the mass function of $X$ at $S$; $X$ is $\varepsilon$-biased exactly when $|\mathrm{bias}_X(S)| \le \varepsilon$ for every nonempty $S$, and *$k$-wise $\varepsilon$-biased* if this holds for every nonempty $S$ with $|S| \le k$. A sample space $G : \sigma \to \{0,1\}^n$ with seed set $\sigma$ is $\varepsilon$-biased if the image of the uniform seed is.

## Depends on

- [Distinguishing advantage](../../../ComputerScience/cryptography/security-games/games-and-advantages/advantage.md)
- [Fourier–Walsh coefficient under the uniform measure](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-fourier-coeff.md)
- [Uniform distribution on a finite type](../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing 22(4), 1993.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992, Definition 3.
