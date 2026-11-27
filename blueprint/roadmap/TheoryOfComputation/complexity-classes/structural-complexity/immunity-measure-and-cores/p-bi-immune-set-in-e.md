# Balcázar–Schöning: E contains P-bi-immune sets

There is a language in $\mathsf{E}=\mathsf{DTIME}(2^{O(n)})$ that is $\mathsf{P}$-bi-immune; hence so does $\mathsf{EXP}$.

## Proof sketch

Slow diagonalization over all machines with polynomial clocks: at each stage, the least-priority requirement whose machine accepts infinitely often (on inputs it claims are in or out) acts by putting an accepted string on the opposite side; each stage simulates only machines with small indices for $2^{O(n)}$ steps.

## Depends on

- [P-immune and P-bi-immune sets; complexity cores](p-immune-sets-and-cores.md)
- [The class E](../../time-and-space-complexity-classes/e.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../../../hierarchy-theorems-and-barriers/time-hierarchy-theorem/time-hierarchy.md)

## Sources

- José L. Balcázar and Uwe Schöning, "Bi-immune sets for complexity classes", Mathematical Systems Theory 18(1), 1985.
