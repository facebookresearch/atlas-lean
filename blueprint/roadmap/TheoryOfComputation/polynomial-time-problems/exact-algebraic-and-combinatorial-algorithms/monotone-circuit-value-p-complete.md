# Goldschlager: the monotone circuit value problem is P-complete

Evaluating a monotone Boolean circuit (gates AND, OR and constants, no negation) on a given input is $\mathsf{P}$-complete under logarithmic-space many-one reductions.

## Proof sketch

It is a special case of the circuit value problem. Hardness: push negations to the inputs by De Morgan's laws, computing in logspace a 'dual-rail' monotone circuit that has gates for both each value and its complement.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)
- [The Circuit Value Problem](../../completeness-other-classes/circuit-value-problem/cvp-dec.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [The Circuit Value Problem is P-complete](../../completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- Leslie M. Goldschlager, "The Monotone and Planar Circuit Value Problems Are Log Space Complete for P", ACM SIGACT News 9(2), 25–29, 1977.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
