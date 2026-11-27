# Quadratic completeness of semifilter covers

Conversely to the fusion lower bound, a semifilter cover of length $t$ for $(T;S_1,\dots,S_n)$ yields an acyclic monotone set circuit computing $T$ from $S_1,\dots,S_n$ with exactly $t^2$ intersection (AND) gates, unions and constants being free; counting every gate, it has at most $4(t+1)^2(n+t+1)$ gates. Hence the cover complexity and monotone AND complexity are polynomially related: $\mathrm{cover}(f)\le\mathrm{AND}(f)\le\mathrm{cover}(f)^2$.

## Proof sketch

Run $t$ synchronous rounds of a closure computation: in each round recompute, for each pair, the intersection of the current unions of supplied sets and earlier pair outputs; at each point of $U$ only the $t$ pair coordinates can change, so $t$ rounds reach the least fixed point, which equals $T$ by the cover property.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Proof depends on

- [Semifilter covers lower-bound the AND count of monotone circuits](fusion-covers-lower-bound-and-gates.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
