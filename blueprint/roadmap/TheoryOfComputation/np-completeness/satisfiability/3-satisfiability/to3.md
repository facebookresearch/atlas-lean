# The SAT-to-3SAT translation

For a CNF formula with clauses $C_1, \dots, C_m$, the
translation is the concatenation, in order, of the chains of clauses replacing $C_1, \dots, C_m$,
where the chain for $C_i$ uses fresh numbers from $u_i = \sum_{j > i} \max(|C_j| - 1, 0)$ on.
