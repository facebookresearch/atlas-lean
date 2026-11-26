# An explicit finite B_k-sequence of size n with entries n^{k+o(k)}

For all $n\ge 0$ and $k\ge1$ there is an explicitly constructed sequence $h_1<\dots<h_n$ of natural numbers forming a $B_k$-set (all sums of $k$ elements, with repetition, are distinct up to order) with $h_n<\bigl((n+2)(2\log_2(n+2)+4)\bigr)^k=n^{k+o(k)}$. It consists of the base-$5$ discrete logarithms modulo $2^{r}$ of the first $n$ odd primes, for $r=\max(3,1+\lceil\log_2 p_n^k\rceil)$.

## Proof sketch

$5$ generates a cyclic subgroup of index two in $(\mathbb{Z}/2^r)^\times$, so discrete logarithms modulo $2^{r-2}$ of odd numbers $\equiv1\pmod 4$ (after a sign) exist. A collision of $k$-sums of logarithms gives a collision of products of $k$ primes modulo $2^r$; since such products are below $2^r$, the products are equal as integers and unique factorization gives equal multisets.

## Depends on

- [$B_h$-set](../../../../Combinatorics/additive-combinatorics/sidon-sets-difference-sets/b-h-sets/is-bh-set.md)

## Sources

- Igor S. Sergeev, "An Explicit Finite B_k-Sequence", 2023.
