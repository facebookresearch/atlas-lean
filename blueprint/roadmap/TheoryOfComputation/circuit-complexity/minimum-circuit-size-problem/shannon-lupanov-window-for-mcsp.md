# The Shannon–Lupanov window for MCSP

There is an absolute constant $c$ such that every Boolean function on $n$ inputs has a De Morgan circuit of size at most $c\, 2^n / n$ (Lupanov), so every truth table is a yes-instance of $\mathrm{MCSP}[s]$ once $s(n) \ge c\,2^n/n$; conversely, the number of functions with circuits of size at most $2^n/(c\, n)$ is at most $2^{2^n/2}$, so for thresholds below $2^n/(cn)$ almost every truth table is a no-instance. Thus the answer to MCSP on random truth tables changes only for thresholds between $2^n/(c\,n)$ and $c\,2^n/n$.

## Proof sketch

Upper bound: Lupanov's representation splits the variables, precomputes all functions of a small block, and assembles $f$ from them with $(1 + o(1))2^n/n$ gates. Lower bound: a circuit with $s$ gates is described by $O(s \log s)$ bits, so at most $2^{O(s\log s)}$ functions have size $s$, which is $o(2^{2^n})$ for $s \le 2^n/(cn)$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- C. E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 1949.
- O. B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya VUZ Radiofizika 1, 1958.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
