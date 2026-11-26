# Square-root circuit bound for fixed powers

In the setting of the fixed-power theorem with $|S|=M$, let $s'=s+(n+1)^3$. Then $f^T$ agrees on $S$ with a circuit of size at most $80000\bigl(s'+\sqrt{(n+1)^3 M s'}\bigr)$. In particular every fixed power of an $n$-bit map with circuits of size $s$ has circuits of size at most $120000\,(s+(n+1)^3)\,2^{(n+1)/2}$, and if the transition map has circuits of polynomial size then all its fixed powers have circuits of size $\mathrm{poly}(n)\cdot 2^{n/2}$.

## Proof sketch

Balance the two terms $Ls$ and $(n+1)^3M/L$ by choosing $L\approx\sqrt{(n+1)^3M/s'}$; rounding the real optimum to an integer costs at most a factor two.

## Depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)

## Proof depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
