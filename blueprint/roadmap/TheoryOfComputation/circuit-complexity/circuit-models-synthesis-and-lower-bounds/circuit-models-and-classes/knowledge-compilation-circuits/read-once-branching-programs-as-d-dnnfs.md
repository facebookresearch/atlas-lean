# Read-once branching programs compile into d-DNNFs

A read-once branching program (free binary decision diagram) on $n$ variables with $N$ decision nodes computing $f$ is converted in linear time into a d-DNNF computing $f$ with at most $3N+2n+2$ nodes; in particular ordered binary decision diagrams (OBDDs) and FBDDs are linearly translatable into d-DNNF.

## Proof sketch

Each decision node on $x_i$ becomes $(x_i\wedge\text{high})\vee(\neg x_i\wedge\text{low})$, sharing the $2n$ literal nodes and the two constant sinks; the disjunction is deterministic because the two branches disagree on $x_i$, and the conjunctions are decomposable because each variable is read at most once along every path.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)
- [Deterministic and nondeterministic branching programs](../branching-programs/branching-programs.md)

## Sources

- Adnan Darwiche, "Decomposable Negation Normal Form", Journal of the ACM 48(4), 2001.
- Adnan Darwiche, Pierre Marquis, "A Knowledge Compilation Map", Journal of Artificial Intelligence Research 17, 229–264, 2002.
