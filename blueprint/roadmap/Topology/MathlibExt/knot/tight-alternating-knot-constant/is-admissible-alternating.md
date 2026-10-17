---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Topology.Knot.TightAlternatingKnot.IsAdmissibleAlternating
---

# Is Admissible Alternating

A real constant `c` is admissible for the tight alternating-knot
inequality when every oriented labeled link type that admits an
alternating diagram and whose crossing number is a finite natural
`k` has type ropelength at least `c * k`, with the inequality read in
`ℝ≥0∞`. On this domain the finite-crossing restriction costs
nothing: the alternating representative itself has a regular
projection, so every such type has finite crossing number
(`crossingNumber_lt_top_of_admitsAlternatingDiagram` below).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Parametrized Link](../euclidean-link/part-01/parametrized-link.md)
- [Admits Alternating Diagram](../regular-projection/part-04/admits-alternating-diagram.md)
- [Crossing Number](../regular-projection/part-03/crossing-number.md)
- [Ropelength](../euclidean-link/part-01/ropelength.md)

## Sources

- [MathlibExt, MathlibExt.Topology.Knot.TightAlternatingKnotConstant](../../../../../sources/v2/MathlibExt.md)
