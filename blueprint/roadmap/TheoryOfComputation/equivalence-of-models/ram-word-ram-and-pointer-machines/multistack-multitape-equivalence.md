# Multi-stack machines and multi-tape Turing machines simulate each other in polynomial time and space

Every deterministic multi-tape Turing machine is simulated by a finite multi-stack (two stacks per tape) machine step by step with constant overhead and with stack storage equal to the visited work space; conversely every finite multi-stack machine running in time $t$ and stack space $s$ is simulated by a multi-tape Turing machine in time $\mathrm{poly}(t)$ and space $O(s)$. Consequently polynomial time, polynomial space and computability agree for the two models, and every partial computable function is computed by a multi-tape Turing machine.

## Proof sketch

A tape is the pair of stacks of cells to the left and right of the head; a head move pops one stack and pushes the other. Conversely each stack is a work tape with the head at its top; one stack instruction costs $O(1)$ tape steps plus a bounded scan for multi-symbol operations.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Polynomial time on single-tape machines](../../complexity-classes/polynomial-time-on-single-tape-machines/single-tape-p.md)

## Proof depends on

- [Quadratic overhead of the single-tape emulation](../../complexity-classes/quadratic-overhead-of-single-tape-simulation/exists-tm0-run-of-tm2-run.md)

## Sources

- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
