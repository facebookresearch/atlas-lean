# One-hot CNF encoding of finite-domain CSPs

Let $F$ be a CSP instance over the domain $\{0,\dots,q-1\}$ on variables $v < N$. Introduce Boolean variables $x_{v,a}$ for $v < N$ and $a < q$, impose the exactly-one constraint on $(x_{v,0},\dots,x_{v,q-1})$ for every $v$, and for each constraint $(R, (v_1,\dots,v_r))$ and each disallowed tuple $(a_1,\dots,a_r) \notin \mathrm{sem}(R)$ add the clause $\bigvee_i \neg x_{v_i, a_i}$. The resulting CNF formula is satisfiable iff $F$ is, and its models are in bijection with the solutions of $F$; it has $qN$ variables, and for scopes of length at most $k$ at most $N(1 + q^2) + |F| q^k$ clauses.

## Proof sketch

Exactly-one constraints make a model encode an assignment $\sigma$; the forbidding clauses exclude exactly the local patterns violating constraints.

## Depends on

- [Finite-domain constraint satisfaction problems](finite-domain-constraint-satisfaction.md)
- [Exactly-one (one-hot) constraint in CNF](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/exactly-one-cnf-constraint.md)

## Sources

- T. Walsh, "SAT v CSP", Principles and Practice of Constraint Programming — CP 2000, LNCS 1894, 441–456, 2000.
