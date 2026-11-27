# Hearn–Demaine: planar AND/OR constraint-logic reachability is PSPACE-complete

The AND/OR NCL reachability problems remain $\mathsf{PSPACE}$-complete when restricted to graphs that are planar (whose incidence graph has a polygonal embedding in the plane); the embedding need not be part of the input, and planarity itself is checked in $\mathsf{NP}$ via rotation certificates.

## Proof sketch

Draw the hard instances with crossings and replace each crossing by a planar crossover gadget made of AND and OR vertices (built from half-crossovers) that transmits each signal independently; reachability questions are preserved.

## Depends on

- [Nondeterministic constraint logic (AND/OR constraint graphs)](nondeterministic-constraint-logic.md)

## Proof depends on

- [Hearn–Demaine: AND/OR constraint-logic reachability is PSPACE-complete](and-or-ncl-pspace-complete.md)
- [Planarity of multigraphs is in NP via rotation systems](../../np-completeness/boolean-constraint-satisfaction/planarity-in-np-via-rotations.md)

## Sources

- Robert A. Hearn and Erik D. Demaine, "PSPACE-completeness of sliding-block puzzles and other problems through the nondeterministic constraint logic model of computation", Theoretical Computer Science 343(1–2), 2005, Theorem 9.
