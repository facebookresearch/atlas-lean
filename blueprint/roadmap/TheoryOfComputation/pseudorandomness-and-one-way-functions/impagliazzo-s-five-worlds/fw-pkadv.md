# Eavesdropping advantage against a public-key scheme

Let $G$ (key generation) and $E$
(encryption) be maps from bitstrings to bitstrings, let $C$ be an encoded flat Boolean circuit,
let $\ell$ be a polynomial with natural-number coefficients and let $n$ be a natural number. For
key coins $r$ and encryption coins $s$, each a string of $\ell(n)$ bits, and a bit $b$, let $pk$
be the first component of the key pair of $G$ on $r$, and let the ciphertext $e$ be $E$ applied
to the bitstring encoding of the triple $(pk, (b), s)$, where $(b)$ is the one-bit list. The
circuit $C$ succeeds on $(r, s, b)$ when it has a last gate value on the bitstring encoding of
the pair $(pk, e)$ and that value equals $b$. If $N$ is the number of triples $(r, s, b)$ on
which $C$ succeeds, the advantage of $C$ at length $n$ is $|N / 2^{2\ell(n) + 1} - 1/2|$.
