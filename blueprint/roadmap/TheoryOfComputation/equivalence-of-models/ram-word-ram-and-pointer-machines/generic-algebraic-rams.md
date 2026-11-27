# Generic (algebraic) RAMs over arbitrary data

A **generic RAM** over a data model is a program with natural-number control labels whose registers and memory cells hold values from an arbitrary set $D$ (e.g. integers, rationals or real algebraic numbers), with a signature of operations and tests on $D$, a set of constants, and a partial map interpreting certain values as memory addresses. Execution follows the instructions deterministically; an execution halts with a unique output and a unique instruction count. Exact algebraic RAMs (over $\mathbb{Q}$ or $\mathbb{Z}$ with exact arithmetic) are simulated by bounded-precision RAMs, and hence by Turing machines, with polynomial overhead when the bit lengths of all values remain polynomially bounded.

## Depends on

- [Output of a RAM machine](../random-access-machines/ram-eval.md)

## Sources

- Peter Bürgisser, Michael Clausen and M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
- Michael Ben-Or, "Lower Bounds for Algebraic Computation Trees", Proceedings of the 15th Annual ACM Symposium on Theory of Computing (STOC 1983), 1983.
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
