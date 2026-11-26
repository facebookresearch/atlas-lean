# Repeated squaring separates unit-cost and logarithmic-cost RAM time

A RAM with multiplication computes $k\mapsto 2^{2^{k}}$ by repeated squaring in $O(k)$ instructions under the **unit-cost** measure (one unit per instruction), whereas under the **logarithmic-cost** measure (each instruction charged the bit lengths of its operands) any computation producing $2^{2^k}$ costs at least $2^{k}$. Hence unit cost with multiplication is not polynomially related to logarithmic cost or to Turing-machine time; for additive RAMs (no multiplication) the two measures are polynomially related.

## Proof sketch

The loop squares a register $k$ times; the result has $2^{k}+1$ bits, and writing it costs at least its length under logarithmic cost.

## Depends on

- [Output of a RAM machine](../random-access-machines/ram-eval.md)

## Sources

- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
