# Decision trees of depth t give DNFs and CNFs of width t

If $f : \{0,1\}^n \to \{0,1\}$ is computed by a decision tree of depth $t$, then $f$ is computed by a DNF whose terms are the consistent paths to $1$-leaves and by a CNF whose clauses are the negations of the consistent paths to $0$-leaves; a path is *consistent* if it never gives two different answers to the same variable (inconsistent paths are reached by no input and are omitted). Each term and clause reads each variable at most once and has at most $t$ literals. Hence the DNF width and CNF width of $f$ are at most its decision tree complexity, and certificates of size at most $t$ exist for every input.

## Proof sketch

An input reaches exactly one leaf; it satisfies the term of a $1$-leaf path iff it follows that path. On a consistent path a variable queried twice gets the same answer both times, so its repeated literal can be dropped; an inconsistent path must be discarded rather than shortened, since dropping its contradictory repeat would turn it into a term satisfied by inputs that reach a different leaf.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)
- [Disjunctive normal form](../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/disjunctive-normal-form.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
