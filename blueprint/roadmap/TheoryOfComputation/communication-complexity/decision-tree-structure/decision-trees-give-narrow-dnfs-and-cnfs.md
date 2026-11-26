# Decision trees of depth t give DNFs and CNFs of width t

If $f : \{0,1\}^n \to \{0,1\}$ is computed by a decision tree of depth $t$, then $f$ is computed by a DNF whose terms are the paths to $1$-leaves and by a CNF whose clauses are the negations of the paths to $0$-leaves. Each term and clause reads each variable at most once and has at most $t$ literals. Hence the DNF width and CNF width of $f$ are at most its decision tree complexity, and certificates of size at most $t$ exist for every input.

## Proof sketch

An input reaches exactly one leaf; it satisfies the term of a $1$-leaf path iff it follows that path. A variable queried twice on a path follows its first answer, so repeated queries can be dropped.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
