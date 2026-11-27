# P/poly is uncountable and contains undecidable languages

The class $\mathsf{P}/\mathsf{poly}$ of languages over $\{0,1\}$ with polynomial-size circuit families is uncountable. Since only countably many languages are decided by Turing machines, $\mathsf{P}/\mathsf{poly}$ contains undecidable languages. (One witness: every unary language is in $\mathsf{P}/\mathsf{poly}$; another: every P-selective set is in $\mathsf{P}/\mathsf{poly}$ by Ko's theorem, and there are uncountably many P-selective sets.)

## Proof sketch

The unary languages $\{1^n: n\in A\}$ for $A\subseteq\mathbb{N}$ are uncountably many and all have circuits of linear size; machines are countable.

## Depends on

- [Polynomial time with polynomial advice](../../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Sparse languages have polynomial-size circuits](../../circuit-synthesis-and-upper-bounds/circuit-synthesis-upper-bounds/sparse-languages-have-polynomial-size-circuits.md)

## Sources

- Ker-I Ko, "On Self-Reducibility and Weak P-Selectivity", Journal of Computer and System Sciences 26(2), 209–221, 1983.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
