# The Zhegalkin basis and multiplicative complexity

The *Zhegalkin basis* is $\{\oplus,\wedge,1\}$: binary exclusive or, binary conjunction and the constant $1$. It is functionally complete, since $\neg x = x\oplus 1$, $x\vee y = x\oplus y\oplus (x\wedge y)$, and every De Morgan circuit is simulated gate by gate. The *multiplicative complexity* $M(f)$ of a Boolean function (or of a system of Boolean functions) $f$ is the least number of $\wedge$ gates in a circuit over $\{\oplus,\wedge,1\}$ computing $f$, with $\oplus$ gates and constants free and depth and fan-out unrestricted. Equivalently, $M(f)$ is the least number of non-affine gates in a circuit over the full binary basis $B_2$.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [The full binary basis B2 and the basis U2](full-binary-basis-b2-and-u2.md)

## Sources

- Joan Boyar, René Peralta and Denis Pochuev, "On the multiplicative complexity of Boolean functions over the basis $(\wedge, \oplus, 1)$", Theoretical Computer Science 235(1), 2000, pp. 43–57.
