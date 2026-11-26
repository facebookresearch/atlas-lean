# Ren–Santhanam–Wang: E^NP circuit lower bounds are equivalent to circuit analysis with E^NP preprocessing

For typical circuit classes and size bounds, circuit lower bounds for $\mathrm{E}^{\mathrm{NP}}$ are equivalent to circuit-analysis algorithms that are allowed an $\mathrm{E}^{\mathrm{NP}}$ preprocessing phase. The equivalence holds in both the infinitely-often and the almost-everywhere settings and extends to larger, for instance subexponential, size bounds.

## Proof sketch

One direction is the $\mathrm{FP}^{\mathrm{NP}}$ framework applied to Avoid for the truth-table map of the class, which yields a hard truth table and hence an $\mathrm{E}^{\mathrm{NP}}$ lower bound. Conversely, a hard truth table computed in $\mathrm{E}^{\mathrm{NP}}$ serves as preprocessing from which analysis algorithms are built by hardness-randomness.

## Depends on

- [The class E](../../time-and-space-complexity-classes/e.md)

## Proof depends on

- [Ren–Santhanam–Wang: FP^NP algorithms for C-Avoid from circuit-analysis data structures](rsw-avoid-from-circuit-analysis.md)
- [Korten: P^NP algorithms for Avoid are equivalent to 2^Ω(n) circuit lower bounds for E^NP](korten-enp-lower-bounds-equivalence.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
