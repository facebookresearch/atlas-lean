# Hearn–Demaine: AND/OR constraint-logic reachability is PSPACE-complete

All three reachability problems of AND/OR NCL (configuration-to-configuration, configuration-to-edge, and edge-to-edge) are $\mathsf{PSPACE}$-complete under polynomial-time many-one reductions, already on AND/OR constraint graphs (Theorem 5 for configuration-to-edge, Corollary 6 for the other two). The input model allows loops and parallel edges, and the hard instances built in the proof use a loop.

## Proof sketch

Membership: configurations have one bit per edge, so reachability is a nondeterministic polynomial-space search, and Savitch's theorem determinizes it. Hardness: reduce TQBF in alternating prenex CNF by chaining quantifier gadgets (existential and universal 'latches' built from AND/OR vertices) to a CNF evaluation network of AND and OR vertices; the target edge can be reversed iff the formula is true.

## Depends on

- [Nondeterministic constraint logic (AND/OR constraint graphs)](nondeterministic-constraint-logic.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../complexity-classes/savitch.md)
- [TQBF is PSPACE-complete](../true-quantified-boolean-formulas/tqbf-pspace-complete.md)
- [Polynomial-length games reduce to TQBF](../../complexity-classes/space-and-time-complexity/alternating-time-and-space/games-reduce-to-tqbf.md)

## Sources

- Robert A. Hearn and Erik D. Demaine, "PSPACE-completeness of sliding-block puzzles and other problems through the nondeterministic constraint logic model of computation", Theoretical Computer Science 343(1–2), 2005, Theorem 5 and Corollary 6.
