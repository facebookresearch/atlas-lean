# The Zhegalkin basis and multiplicative complexity

The *Zhegalkin basis* is $\{\oplus,\wedge,1\}$: binary exclusive or, binary conjunction and the constant $1$. It is functionally complete, since $\neg x = x\oplus 1$, $x\vee y = x\oplus y\oplus (x\wedge y)$, and every De Morgan circuit is simulated gate by gate. The *multiplicative complexity* $M(f)$ of a Boolean function (or of a system of Boolean functions) $f$ is the least number of $\wedge$ gates in a circuit over $\{\oplus,\wedge,1\}$ computing $f$, with $\oplus$ gates and constants free and depth and fan-out unrestricted. Equivalently, over any basis of fan-in at most two, $M(f)$ is the least number of non-affine gates.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [The full binary basis B2 and the basis U2](full-binary-basis-b2-and-u2.md)

## Sources

- Igor S. Sergeev, "A relation between additive and multiplicative complexity of Boolean functions", 2013.
- Anastasiya Chistopolskaya, Vladimir V. Podolskii, "Parity Decision Tree Complexity is Greater Than Granularity", 2018.
