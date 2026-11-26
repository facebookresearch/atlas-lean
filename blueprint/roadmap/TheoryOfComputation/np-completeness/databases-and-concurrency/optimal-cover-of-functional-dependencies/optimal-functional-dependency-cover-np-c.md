# OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES is NP-hard under Turing reductions

The [decision problem](optimal-functional-dependency-cover-dec.md) for OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES, which accepts exactly the bitstrings that decode to a well-formed instance with a cover of size at most $K$, is NP-hard under polynomial-time Turing reductions. Maier (1980), Theorem 4, reduces MINIMUM CARDINALITY KEY to it: for a set of functional dependencies he derives two sets whose optimal cover sizes $s$ and $t$ give the minimum key size $t - s - 2$, so the reduction asks the decision problem several questions rather than mapping each instance to a single one.

Whether every problem in NP has a polynomial-time many-one reduction to this decision problem, as the Lean statement of NP-completeness asks, is not settled by this source; #10191 tracks a source or argument for it.

## Depends on

- [OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES as a decision problem](optimal-functional-dependency-cover-dec.md)

## Sources

- D. Maier, "Minimum covers in the relational database model", Journal of the ACM 27(4) (1980), 664–674, Theorem 4.
