# Ren–Santhanam–Wang: FP^NP algorithms for C-Avoid from circuit-analysis data structures

Generalizing Williams's connection between circuit-analysis algorithms and circuit lower bounds, for typical multi-output circuit classes $\mathcal{C}$ a slightly non-trivial circuit-analysis data structure for $\mathcal{C}$ yields an $\mathrm{FP}^{\mathrm{NP}}$ algorithm for $\mathcal{C}$-Avoid. As an application there is a non-trivial $\mathrm{FP}^{\mathrm{NP}}$ range avoidance algorithm for De Morgan formulas. A key ingredient is a construction of rectangular PCPs of proximity, building on rectangular PCPs of Bhangale, Harsha, Paradise and Tal.

## Proof sketch

Encode the candidate non-image as a PCP of proximity for the statement that it is in the range; rectangularity lets a data structure for $\mathcal{C}$ evaluate all verifier queries on the given circuit faster than brute force. An $\mathrm{NP}$ oracle then builds a string bit by bit, and a successful fast analysis certifies that the string has no preimage.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Williams: NEXP is not contained in ACC0](../../../circuit-complexity/williams-nexp-not-in-acc0.md)

## Proof depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Williams: NEXP is not contained in ACC0](../../../circuit-complexity/williams-nexp-not-in-acc0.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
