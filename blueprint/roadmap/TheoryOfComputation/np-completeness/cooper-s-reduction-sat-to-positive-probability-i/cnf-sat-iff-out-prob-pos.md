# Reduction correctness for arbitrary CNF formulas

A CNF formula, a finite list of clauses of any lengths, is satisfiable if and only if the output of its network is true with positive probability.

This extends Cooper's construction for 3SAT (Cooper 1990, Sections 4.1–4.2), whose clauses have three literals each and whose clause nodes test those three literals, to arbitrary CNF formulas: each clause is built as a chain of binary OR nodes, and the statement covers the formula with no clauses and formulas containing the empty clause.
