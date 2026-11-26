# 3SAT WITH AT MOST FIVE CLAUSES PER VARIABLE as a decision problem

The decision problem 3SAT WITH AT MOST FIVE CLAUSES PER VARIABLE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a variable count and a CNF formula, to a pair $(n, C)$ such that

- $(n, C)$ is [well-formed](well-formed-3-6.md): every clause of the list $C$ lists exactly three distinct literals on variables below $n$, and for every variable $u < n$ at most five entries of $C$ are clauses containing $u$ or $\bar u$ (a clause containing both signs counts once for $u$, and a repeated clause counts once per entry, so this bounds clauses per variable rather than literal occurrences);
- $C$ is satisfiable: some list of $n$ truth values, read as the values of the variables $0, \dots, n - 1$, satisfies every clause.

It rejects every bitstring that does not decode, or decodes to an instance that is not well-formed.
