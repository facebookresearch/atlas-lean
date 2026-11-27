# Boolean and two-element arithmetic circuits have linearly related sizes

Over the two-element Boolean ring $(\{0,1\},\oplus,\wedge)$, every De Morgan circuit with $s$ gates is simulated by an arithmetic circuit (constants, $+$, $\times$) with at most $3s$ gates, and every arithmetic circuit with $s$ gates is simulated by a De Morgan circuit with at most $4s$ gates; both simulations preserve all inputs and outputs.

## Proof sketch

Over $\mathbb{F}_2$, $\neg x=x+1$ and $x\vee y=x+y+xy$; conversely $x\oplus y=(x\vee y)\wedge\neg(x\wedge y)$ costs four De Morgan gates.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Arithmetic circuit](../../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Boolean circuits are simulated over any ring with size factor five](boolean-circuits-over-any-ring-factor-five.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
