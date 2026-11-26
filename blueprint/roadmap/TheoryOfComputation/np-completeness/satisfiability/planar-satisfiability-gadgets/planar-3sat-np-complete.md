# Lichtenstein: planar 3-SAT is NP-complete

Satisfiability of planar CNF formulas whose clauses have at most three literals is NP-complete. Moreover the reduction from 3-SAT can be made parsimonious, so counting satisfying assignments of planar 3-CNF formulas is $\#\mathsf{P}$-complete.

## Proof sketch

Draw the incidence graph of an arbitrary 3-CNF in the plane with crossings, and replace every crossing of two edges by the crossover gadget, which transmits both values unchanged with a unique internal extension; wires are realized by implication chains. Gluing gadgets with private auxiliary variables preserves satisfiability and model counts.

## Depends on

- [Planar CNF formulas](planar-cnf-formulas.md)

## Proof depends on

- [Lichtenstein's crossover gadget](lichtenstein-crossover-gadget.md)
- [Gluing CNF gadgets with private auxiliary variables](../../../../Logic/propositional-logic/cnf-gadgets-and-encodings/gluing-cnf-gadgets.md)
- [3SAT is NP-complete](../3-satisfiability/sat3-dec-np-complete.md)

## Sources

- D. Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 329–343, 1982.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998.
