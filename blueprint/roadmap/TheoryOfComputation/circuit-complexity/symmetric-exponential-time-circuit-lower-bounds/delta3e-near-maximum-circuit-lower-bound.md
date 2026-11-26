# Miltersen–Vinodchandran–Watanabe: E^Σ2P contains a language of circuit complexity at least 2^n/n

$\Delta_3\mathrm{E}=\mathrm{E}^{\Sigma_2\mathrm{P}}$ contains a language $L$ such that for all large $n$ the slice $L\cap\{0,1\}^n$ has no circuit of size $2^n/n$. Before 2023 this was the smallest uniform class known to require exponential circuit size; for $\Sigma_2\mathrm{E}$ and its relatives only half-exponential lower bounds were known.

## Proof sketch

By Shannon's counting argument, for large $n$ some truth table of length $2^n$ has circuit complexity above $2^n/n$. Define $L$ on length $n$ by the lexicographically first such truth table. It is found bit by bit: for a prefix $p$, the question whether some extension of $p$ has no circuit of size $2^n/n$ is a $\Sigma_2$ question of length $2^{O(n)}$, answered by the $\Sigma_2\mathrm{P}$ oracle in exponential time.

## Depends on

- [The universal levels of the polynomial hierarchy](../../complexity-classes/time-and-space-complexity-classes/pi-k.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Peter Bro Miltersen, N. V. Vinodchandran and Osamu Watanabe, "Super-polynomial versus half-exponential circuit size in the exponential hierarchy", COCOON (1999).
- Lijie Chen, Shuichi Hirahara and Hanlin Ren, "Symmetric Exponential Time Requires Near-Maximum Circuit Size", STOC (2024), arXiv:2309.12912.
