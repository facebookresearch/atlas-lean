# Boolean circuits are simulated over any ring with size factor five

Let $R$ be any ring with $1_R\ne 0_R$ and represent the Boolean values $0,1$ by $0_R,1_R$. Every De Morgan circuit with $s$ gates, $n$ inputs and $m$ outputs has an arithmetic circuit over $R$ (with constant, addition and multiplication gates) of at most $5s$ gates that, on every $0/1$-valued input, outputs the $0/1$ representations of all $m$ outputs. Here AND is multiplication, NOT is $1+(-1)\cdot x$ and OR is $(x+y)+(-1)\cdot(xy)$.

## Proof sketch

Replace each gate by the corresponding expression; each uses at most five arithmetic gates, constants included, and the identities hold on $\{0_R,1_R\}$.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Arithmetic circuit](../../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
