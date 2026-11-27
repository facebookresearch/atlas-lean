# Kabanets–Cai: if MCSP is in BPP, there are no one-way functions

If $\mathrm{MCSP} \in \mathsf{BPP}$, then every keyed function family computable in polynomial time is distinguished from a uniformly random function by a probabilistic polynomial-time oracle adversary with advantage at least $1/4$ for all large $n$. Consequently no pseudorandom function family exists, and hence no one-way function exists.

## Proof sketch

The adversary queries the oracle on all inputs of a block of $m = O(\log n)$ bits to obtain a truth table of length $2^m$, and asks the MCSP decider whether it has circuits of size $n^c$. The truth table of $F_k$ restricted to such a block has small circuits, while a random function's truth table almost surely has circuit complexity near $2^m/m$ by counting.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [One-way functions imply adaptively secure pseudorandom functions](../hard-core-predicates-and-stretch/one-way-functions-imply-pseudorandom-functions.md)

## Sources

- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC), 2000.
