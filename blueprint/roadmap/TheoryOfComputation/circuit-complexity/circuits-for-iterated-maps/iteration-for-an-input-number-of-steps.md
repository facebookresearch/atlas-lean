# Iterating a circuit for a number of steps given as input

Let $f:\{0,1\}^n\to\{0,1\}^n$ have a circuit of size $s$. There is a circuit with $n+m$ inputs which, on a state $x$ and an $m$-bit number $T$, outputs $f^{T}(x)$, of size at most $m$ times the fixed-power bound plus $4nm$; in particular of size $O\bigl(m(s+(n+1)^3)2^{n/2}\bigr)$. Long input times cost only an additive overhead: the state after $T$ steps can be computed from a fixed power landing on the eventual cycle together with the residue of $T$ modulo the cycle length.

## Proof sketch

Binary powering: stage $j$ applies a circuit for $f^{2^j}$ and bit $j$ of $T$ selects between its output and the current state, at four gates per state bit. For large $T$, reduce $T$ modulo the cycle length once the orbit is periodic.

## Depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)

## Proof depends on

- [Square-root circuit bound for fixed powers](square-root-bound-for-fixed-powers.md)
- [Circuits for transient depths, cycle labels, reachability and hitting times](circuits-for-reachability-and-hitting-times.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
- Christian Reitwiessner, "Input-time iteration in O(B+nm) gates", 2026.
