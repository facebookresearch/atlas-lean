# Ren–Santhanam–Wang: E^NP circuit lower bounds are equivalent to circuit analysis with E^NP preprocessing

For $\mathcal{C}\in\{\mathrm{TC}^0,\mathrm{NC}^1,\mathrm{P/poly}\}$ the following are equivalent: $\mathrm{E}^{\mathrm{NP}}$ cannot be computed by polynomial-size $\mathcal{C}$ circuits on almost every input length; there is a non-trivial GapUNSAT algorithm for $\mathcal{C}$ circuits with an $\mathrm{E}^{\mathrm{NP}}$ preprocessing phase. For classes $\mathcal{C}$ that may not compute MAJORITY (under mild closure properties), $\mathrm{E}^{\mathrm{NP}}$ cannot be $(1/2+1/\mathrm{poly}(n))$-approximated by $\mathcal{C}$ circuits on almost every input length if and only if there is a non-trivial CAPP algorithm for $\mathcal{C}$ circuits with inverse-circuit-size error and $\mathrm{E}^{\mathrm{NP}}$ preprocessing.

## Proof sketch

One direction is the $\mathrm{FP}^{\mathrm{NP}}$ framework applied to Avoid for the truth-table map of the class, which yields a hard truth table and hence an $\mathrm{E}^{\mathrm{NP}}$ lower bound. Conversely, a hard truth table computed in $\mathrm{E}^{\mathrm{NP}}$ serves as preprocessing from which analysis algorithms are built by hardness-randomness.

## Depends on

- [The class E](../../time-and-space-complexity-classes/e.md)

## Proof depends on

- [Ren–Santhanam–Wang: FP^NP algorithms for C-Avoid from circuit-analysis data structures](rsw-avoid-from-circuit-analysis.md)
- [Korten: P^NP algorithms for Avoid are equivalent to 2^Ω(n) circuit lower bounds for E^NP](korten-enp-lower-bounds-equivalence.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
