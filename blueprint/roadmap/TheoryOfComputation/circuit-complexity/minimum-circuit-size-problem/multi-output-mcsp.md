# Multi-output MCSP

*Multi-output MCSP* is the language of tuples $(1^n, 1^m, 1^s, T_1, \dots, T_m)$ with $T_j \in \{0,1\}^{2^n}$ such that a single De Morgan circuit with $n$ inputs and $m$ outputs, of size at most $s$, computes the functions with truth tables $T_1, \dots, T_m$ at its outputs. It is in NP, since a certificate is such a circuit.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)

## Sources

- R. Ilango, B. Loff and I. C. Oliveira, "NP-Hardness of Circuit Minimization for Multi-Output Functions", Computational Complexity Conference (CCC) 2020.
