# AWPP is low for PP, and BQP ⊆ AWPP

$\mathsf{PP}^{A}=\mathsf{PP}$ for every $A\in\mathsf{AWPP}$. Moreover $\mathsf{BQP}\subseteq\mathsf{AWPP}$ (Fortnow–Rogers), hence $\mathsf{BQP}$ is low for $\mathsf{PP}$: $\mathsf{PP}^{\mathsf{BQP}}=\mathsf{PP}$.

## Proof sketch

Weight each guessed oracle answer by the amplified AWPP gap fraction, which is within $2^{-q}$ of the indicator of the correct answer; with $q$ larger than the number of queries times the PP gap's bit length, the accumulated errors cannot change the sign of the PP gap. The acceptance probability of a Hadamard–Toffoli circuit is a $\mathsf{GapP}$ function divided by $2^{h}$, giving $\mathsf{BQP}\subseteq\mathsf{AWPP}$.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)
- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)
- [BQP is contained in PP](../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/bqp-subset-pp.md)

## Sources

- Stephen A. Fenner, "PP-Lowness and a Simple Definition of AWPP", Theory of Computing Systems 36(2), 2003.
- Stephen A. Fenner, Lance J. Fortnow, Stuart A. Kurtz and Lide Li, "An Oracle Builder's Toolkit", Information and Computation 182(2), 2003, Section 6.1.
- Lance Fortnow and John Rogers, "Complexity Limitations on Quantum Computation", Journal of Computer and System Sciences 59(2), arXiv:cs/9811023, 1999.
