# Deterministic square roots modulo a prime given a quadratic non-residue

There is a deterministic polynomial-time algorithm that, given a prime $P$, a quadratic residue $s$ modulo $P$ and, when $P\equiv1\pmod 4$, a quadratic non-residue $t$ modulo $P$, outputs $y$ with $y^{2}\equiv s\pmod P$. If $P\equiv3\pmod4$, then $y=s^{(P+1)/4}$ works. In general the algorithm computes an odd $e$ and an even $e'$ with $s^{e}t^{e'}\equiv1\pmod P$, after which $y=s^{(e+1)/2}t^{e'/2}$ satisfies $y^2\equiv s$.

## Proof sketch

Write $P-1=2^{k}m$ with $m$ odd. Starting from $s^{(P-1)/2}=1$, repeatedly halve the exponent of $s$; whenever the current power of $s$ times the accumulated power of $t$ equals $-1$, multiply by $t^{(P-1)/2}$, which is $-1$ because $t$ is a non-residue. This maintains $s^{e}t^{e'}=1$ until $e$ becomes odd, with $e'$ even throughout.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 6.16, Items 1–3 (numbering of the 2007 public draft).
