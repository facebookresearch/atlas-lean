# Korten: P^NP algorithms for Avoid are equivalent to 2^Ω(n) circuit lower bounds for E^NP

There is a deterministic polynomial-time algorithm with an $\mathrm{NP}$ oracle for Avoid if and only if $\mathrm{E}^{\mathrm{NP}}$ contains a language of circuit complexity $2^{\Omega(n)}$. Moreover:

1. $\mathrm{E}^{\mathrm{NP}}$ contains a language of circuit complexity $2^{\Omega(n)}$ if and only if it contains one of circuit complexity $2^n/(2n)$;
2. $\mathrm{EXP}^{\mathrm{NP}}$ contains a language of circuit complexity $2^{n^{\Omega(1)}}$ if and only if it contains one of circuit complexity $2^n/(2n)$.

Every explicit construction problem in $\mathrm{APEPP}$ is either $\mathrm{APEPP}$-complete under $\mathrm{P}^{\mathrm{NP}}$ reductions or solvable infinitely often in subexponential time with an $\mathrm{NP}$ oracle.

## Proof sketch

A $\mathrm{P}^{\mathrm{NP}}$ construction of hard truth tables on input $1^{2^n}$ is the same as an $\mathrm{E}^{\mathrm{NP}}$ language with that hardness. Completeness transfers any such construction, even of weak hardness $2^{\varepsilon n}$, into a $\mathrm{P}^{\mathrm{NP}}$ algorithm for all of $\mathrm{APEPP}$, in particular for near-maximum hard truth tables; padding gives the $\mathrm{EXP}^{\mathrm{NP}}$ version.

## Depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [The total function class TFΣ2P and the explicit-construction class APEPP](tfsigma2p-and-apepp.md)

## Proof depends on

- [Korten: constructing a hard truth table is APEPP-complete under P^NP reductions](korten-hard-truth-table-apepp-complete.md)

## Sources

- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
