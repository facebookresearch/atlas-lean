# Forbidden-pattern compilation of Boolean CSPs to CNF

Let $F$ be an instance of $\mathrm{CSP}(\Gamma)$ in which every scope has length at most $k$. Replacing each constraint $R(v_1,\dots,v_r)$ by the clauses $\bigvee_{i}(v_i \ne w_i)$, one for each forbidden tuple $w \in \{0,1\}^r \setminus R$, gives a $k$-CNF formula $\mathrm{CNF}(F)$ on the same variables with at most $2^k$ clauses per constraint and no auxiliary variables, satisfied by exactly the assignments satisfying $F$. Moreover each violated constraint falsifies exactly one of its clauses, so for every assignment the number of falsified clauses equals the number of violated constraints; hence MAX-CSP values and model counts are preserved.

## Proof sketch

A clause excludes exactly its forbidden local pattern, and a violated constraint exhibits exactly one forbidden pattern even when its scope repeats variables.

## Depends on

- [Boolean constraint languages and CSP(Γ)](boolean-constraint-languages.md)
- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- T. Walsh, "SAT v CSP", Principles and Practice of Constraint Programming — CP 2000, LNCS 1894, 441–456, 2000.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
