# Sequential squaring modulo a squarefree modulus is a single power

Let $M\ge 1$ be squarefree and let $\lambda(M)$ be the exponent of the unit group $(\mathbb{Z}/M\mathbb{Z})^\times$ (Carmichael's function). Then every residue $x\in\mathbb{Z}/M\mathbb{Z}$, unit or not, satisfies $x^{\lambda(M)+1}=x$, and for every $T\ge 0$ the $T$-fold squaring map satisfies

$$
x^{2^T}=x^{e_T}\quad\text{with}\quad e_T=1+\bigl((2^T-1)\bmod\lambda(M)\bigr).
$$

## Proof sketch

By the Chinese remainder theorem it suffices to treat a prime modulus $p\mid M$, where $x^{p}\equiv x$ and $p-1\mid\lambda(M)$, so $x^{\lambda(M)+1}=x$ also for $x\equiv 0$. Two positive exponents congruent modulo $\lambda(M)$ therefore give the same power map.

## Depends on

- [Karatsuba multiplication](../../../ComputerScience/algebraic-and-numerical-algorithms/karatsuba-algorithm/karatsuba.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
