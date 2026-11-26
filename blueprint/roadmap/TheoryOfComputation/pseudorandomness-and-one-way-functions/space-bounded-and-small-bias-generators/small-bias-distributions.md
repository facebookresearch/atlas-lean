# Small-bias distribution and generator

A distribution $D$ on $\{0,1\}^\ell$ is *$\varepsilon$-biased* if for every nonempty set $S \subseteq \{1, \dots, \ell\}$,

$$\mathrm{bias}_S(D) = \Bigl|\Pr_{y \leftarrow D}\Bigl[\bigoplus_{i \in S} y_i = 0\Bigr] - \Pr_{y \leftarrow D}\Bigl[\bigoplus_{i \in S} y_i = 1\Bigr]\Bigr| \le \varepsilon.$$

A generator is an *$\varepsilon$-bias generator* if its output on a uniform seed is $\varepsilon$-biased. The uniform distribution is $0$-biased, and an $\varepsilon$-biased distribution fools every parity test with advantage $\varepsilon/2$.

## Depends on

- [Distinguishing advantage](../../../ComputerScience/cryptography/security-games/games-and-advantages/advantage.md)

## Sources

- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing 22(4), 1993.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
