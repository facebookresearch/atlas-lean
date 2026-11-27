# Boolean and two-element arithmetic circuits have linearly related sizes

Over the two-element Boolean ring $(\{0,1\},\oplus,\wedge)$, the De Morgan basis $\{\wedge,\vee,\neg\}$ and the arithmetic basis $\{+,\times\}$ (with the constants available as inputs) are both complete, and circuit sizes over them differ by at most a constant factor. Precisely, for complete bases $\Omega,\Omega'$ let $c=\max\{C_\Omega(g) : g\in\Omega'\}$; then $C_\Omega(f)\le c\,C_{\Omega'}(f)$ for every Boolean function $f$. Applied in both directions, the De Morgan size and the arithmetic size over $\mathbb{F}_2$ of every Boolean function are within constant factors of each other.

## Proof sketch

Replace every gate of an $\Omega'$-circuit by an optimal $\Omega$-circuit for that gate. Over $\mathbb{F}_2$, $\neg x=x+1$ and $x\vee y=x+y+xy$ (three arithmetic gates), and conversely $x\oplus y=(x\vee y)\wedge\neg(x\wedge y)$ costs four De Morgan gates while $x\wedge y$ costs one. Derived here from these gadgets: every De Morgan circuit with $s$ gates is simulated by an arithmetic circuit with at most $3s$ gates and every arithmetic circuit with $s$ gates by a De Morgan circuit with at most $4s$ gates, with all inputs and outputs preserved.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Circuit complexity, binary cost and formula leaf size](../circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Arithmetic circuit](../../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Boolean circuits are simulated over any field with constant-factor overhead](boolean-circuits-over-any-ring-factor-five.md)

## Sources

- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987 (Chapter 1, Definition 3.3 and Theorem 3.1, pp. 9–10).
