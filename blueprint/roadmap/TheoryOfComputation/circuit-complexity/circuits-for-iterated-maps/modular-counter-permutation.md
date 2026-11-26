# The modular-counter permutation and typical powers

For $k\ge 1$ let $\mathrm{cnt}_k$ be the permutation of $\{0,1\}^{2k}$ that reads its state as a pair $(a,r)$ of $k$-bit numbers and maps it to $(a,(r+1)\bmod a)$ when $a\ge 1$ (and fixes the states with $a=0$). Then $\mathrm{cnt}_k$ has a De Morgan circuit with at most $50k+20$ gates, and its powers $\mathrm{cnt}_k^{T}$ for $0\le T<\mathrm{lcm}(1,2,\dots,2^k-1)$ are pairwise distinct. Since there are only $2^{O(s\log s)}$ circuits of size $s$, most of these exponentially many powers require circuits of size $2^{\Omega(k)}$, although each step is computed in linear size.

## Proof sketch

The power $\mathrm{cnt}_k^T$ adds $T\bmod a$ to the counter of modulus $a$, so it determines $T$ modulo every $a<2^k$ and hence modulo their least common multiple, which is $2^{\Theta(2^k)}$. Counting circuits then shows that a typical power needs exponential size.

## Depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)
- [Counting functions with small De Morgan circuits](../circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Proof depends on

- [Counting functions with small De Morgan circuits](../circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
