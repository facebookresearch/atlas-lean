# Read-once branching programs compile into d-DNNFs

A read-once branching program (an ordered binary decision diagram under an injective variable order) of length $L$ with state set $S$ computing $f$ is converted into a d-DNNF computing $f$ with at most $(L+1)|S|+2L+2L|S|$ nodes.

## Proof sketch

Each decision node on $x_i$ becomes $(x_i\wedge\text{high})\vee(\neg x_i\wedge\text{low})$; the disjunction is deterministic because the two branches disagree on $x_i$, and the conjunctions are decomposable because each variable is read at most once along every path.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)

## Sources

- Marcelo Arenas, Oliver Broadrick, Vincent Liew, Guy Van den Broeck, "d-DNNF is Not Polynomially Closed Under Negation", STOC 2027 submission 1318, 2026.
- Adnan Darwiche, "Decomposable Negation Normal Form", Journal of the ACM, 2001.
