# Pointwise mass bounds from parity biases

For every distribution $X$ on $\{0,1\}^n$ and every $x \in \{0,1\}^n$,

$$
\bigl|2^n \Pr[X = x] - 1\bigr| \le \sum_{\emptyset \ne S \subseteq [n]} |\mathrm{bias}_X(S)| .
$$

Hence an $\varepsilon$-biased $X$ satisfies $|2^n\Pr[X=x] - 1| \le (2^n - 1)\varepsilon$, and if the right-hand side is less than $1$ then $X$ has full support. Bounding only the biases of high-order sets gives a min-entropy lower bound for $X$ (the low-discrepancy lifting variant).

## Proof sketch

Fourier inversion writes $2^n\Pr[X=x] = \sum_S \mathrm{bias}_X(S)(-1)^{\bigoplus_{i\in S}x_i}$, and the $S=\emptyset$ term is $1$; apply the triangle inequality.

## Depends on

- [Bias, ε-biased and k-wise ε-biased distributions](small-bias-distributions.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing, 2021.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
