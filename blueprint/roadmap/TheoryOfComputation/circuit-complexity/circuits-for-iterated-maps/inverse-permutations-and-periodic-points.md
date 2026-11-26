# Inverse permutations and periodic points within the fixed-power bound

If $p$ is a permutation of a finite set with $k$ elements, then $p^{-1}=p^{k!-1}$. Consequently, if a permutation of $\{0,1\}^n$ has a circuit of size $s$, its inverse has a circuit within the fixed-power bound for $s$ (in particular of size $\mathrm{poly}(n,s)\cdot 2^{n/2}$). Similarly, a state $x$ is periodic under $f:\{0,1\}^n\to\{0,1\}^n$ if and only if $f^{(2^n)!}(x)=x$, so periodicity is decided by one fixed-power circuit and an equality test.

## Proof sketch

The order of $p$ in the symmetric group divides $k!$, so $p^{k!}=\mathrm{id}$. Every orbit of $f$ enters its cycle within $2^n$ steps and every cycle length divides $(2^n)!$.

## Depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)

## Proof depends on

- [Square-root circuit bound for fixed powers](square-root-bound-for-fixed-powers.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
