# The complete AND–OR tree is evasive

For every $k \ge 0$ the function computed by the complete binary AND–OR tree $T_{2,k}$ of depth $2k$ on $n = 4^k$ leaves (alternating AND at even levels and OR at odd levels) has deterministic decision tree complexity $n$; the same holds for the complete binary NAND tree of every depth.

## Proof sketch

The top Fourier coefficient of the NAND tree is nonzero: in $\pm1$ form NAND has top coefficient $1/2$, and for a composition $F(G_1(y_1),G_2(y_2))$ with disjoint variable sets the coefficient of the full variable set is $\hat F(\{1,2\})\,\hat G_1(\text{top})\,\hat G_2(\text{top})$, so it is a product of nonzero factors through the levels; since $n=4^k\ge1$, the Rivest–Vuillemin criterion applies. The AND–OR tree of depth $2k$ equals the NAND tree up to negating inputs and output.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Rivest–Vuillemin parity criterion for evasiveness](rivest-vuillemin-parity-criterion.md)

## Sources

- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
- M. Saks and A. Wigderson, "Probabilistic Boolean Decision Trees and the Complexity of Evaluating Game Trees", FOCS 1986.
