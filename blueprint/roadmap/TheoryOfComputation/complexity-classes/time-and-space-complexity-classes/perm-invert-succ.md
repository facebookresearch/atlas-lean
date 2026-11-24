# Inversion success probability against a permutation family

Let $\pi$ be a family of
maps $\pi_n$ from $n$-bit strings to $n$-bit strings, let $A$ be a function sending a natural
number and two bitstrings to a bitstring, and let $n$ and $m$ be natural numbers. For a bitstring
$w$, write $\mathrm{trunc}_n(w)$ for the $n$-bit string whose bit at each position $i < n$ is the
entry of $w$ at position $i$, or false if $w$ has at most $i$ entries. The success probability of
$A$ against $\pi$ at length $n$ with $m$ coins is the rational number $N / 2^{n+m}$, where $N$ is
the number of pairs $(x, c)$ of an $n$-bit string $x$ and an $m$-bit string $c$ with
$\pi_n(\mathrm{trunc}_n(A(n, \pi_n(x), c))) = \pi_n(x)$, where $\pi_n(x)$ is passed to $A$ as a
bitstring.

Here $A$ is a probabilistic inverter that receives the security parameter $n$, the image
$\pi_n(x)$ and the coins $c$.

## Sources

- O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University Press, 2001, Section 2.2.
