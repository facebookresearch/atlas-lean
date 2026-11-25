# Canonical payloads of a decoded pair are bounded by the raw input

For every bit string $x$, if the [decoder of pairs of natural numbers](decode-pair-nat.md) returns $(m, n)$ on $x$,
then the binary codes of $m$ and $n$ have total length at most $|x| + 1$. This holds even when a field of $x$ ends
with a $0$.
