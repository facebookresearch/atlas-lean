# Pointwise mass bounds from parity biases

For every distribution $X$ on $\{0,1\}^n$ and every $x \in \{0,1\}^n$,

$$
\bigl|2^n \Pr[X = x] - 1\bigr| \le \sum_{\emptyset \ne S \subseteq [n]} |\mathrm{bias}_X(S)| .
$$

Hence an $\varepsilon$-biased $X$ satisfies $|2^n\Pr[X=x] - 1| \le (2^n - 1)\varepsilon$, and if the right-hand side is less than $1$ then $X$ has full support. If only the high-order biases are controlled, namely $|\mathrm{bias}_X(S)|\le(2n)^{-|S|}$ for every $S$ with $|S|\ge t\ge1$, then $H_\infty(X)\ge n-t\log_2 n-1$ (vacuous for $n=1$).

## Proof sketch

Fourier inversion writes $2^n\Pr[X=x] = \sum_S \mathrm{bias}_X(S)(-1)^{\bigoplus_{i\in S}x_i}$, and the $S=\emptyset$ term is $1$; apply the triangle inequality. For the min-entropy bound, the sets of size at least $t$ contribute at most $1$ (since $\sum_{i\ge1}\binom ni(2n)^{-i}\le1$) and for $n\ge2$ the sets of size below $t$ (the empty set included) at most $\sum_{i<t}\binom ni\le n^t-1$, so $2^n\Pr[X=x]\le n^t\le 2^{t\log_2 n+1}$.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 171–210, 2021 (numbering of arXiv:1904.13056), Lemmas 2.5 and 2.6 (the triangle-inequality argument and the high-order min-entropy bound).
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 8.5.2.
