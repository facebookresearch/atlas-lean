# Hitting sets for polynomials in small derivative-closed spaces

Over a field of characteristic zero, let $V\subseteq F[x_1,\dots,x_n]$ be a space of dimension at most $r$ closed under all partial derivatives. Then no nonzero $f\in V$ vanishes on the curve $x_i=\ln(1+(i+1)t)$ to order $nr^2+r$ or more. Consequently, if every polynomial of a class lies in such a space and has degree at most $d$, the points of the truncated curve at $t=0,1,\dots,d(nr^2+r)$ form a hitting set; for instance sums of $s$ powers of linear forms of degree $d$ have an explicit hitting set of $d\bigl(n(s(d+1))^2+s(d+1)\bigr)+1$ points.

## Proof sketch

Choose a basis $g_1,\dots,g_r$ of $V$; the Wronskian of the $g_j$ along the derivation tangent to the curve is a polynomial in $t$ alone of degree at most $nr^2$, and it is nonzero by algebraic independence of the curve. If $f\in V$ vanished to high order on the curve, the Wronskian would vanish there too.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [The partial-derivative measure](../algebraic-circuit-lower-bound-methods/partial-derivative-measure.md)

## Proof depends on

- [Algebraic independence of the logarithmic curve](algebraic-independence-of-logarithms.md)
- [The Wronskian of a derivative-closed space depends only on t](wronskian-of-a-derivative-closed-space.md)

## Sources

- Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay et al., "Hitting Sets from Derivations: Waring Rank and Noncommutative ABPs", Electronic Colloquium on Computational Complexity, 2026.
