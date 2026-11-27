# Polynomial CNF decompositions are polynomial monotone circuits

A family of consistency checkers of global constraints has CNF decompositions of polynomial size, propagated by unit propagation, exactly when it has monotone Boolean circuits of polynomial size. A decomposition of a propagator yields one of its induced checker, so polynomial-size decompositions of domain consistency propagators give polynomial-size monotone circuits for satisfiability of the constraint.

Use the notions of [CNF decompositions of propagators and consistency checkers](cnf-decomposition-of-a-propagator.md), including the checker induced by a propagator, and read a consistency checker $f_C$ as the monotone Boolean function of the characteristic vector $(b_{i,j})$ of the domain. For a family $\mathcal F$ of checkers, each on its own instance with $|\mathbf x|$ initial literals, say $\mathcal F$ has polynomial-size decompositions (circuits) if one polynomial $p$ bounds, for every member, the size of some decomposition (circuit) of that member by $p(|\mathbf x|)$. Circuits are [monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md) of fan-in-2 AND and OR gates, extended by the constant inputs 0 and 1; for a checker that is not constant, constants can be eliminated by simplification without increasing size, so the linked constant-free circuits suffice.

1. A CNF decomposition $C_P$ of a propagator $f_P$, given in 3-CNF, converts in polynomial time into a CNF decomposition of size $O(|C_P|)$ of the checker induced by $f_P$. (The source assumes 3-CNF input and notes that longer clauses, such as the at-least-one clauses of the direct encoding, can be split with fresh auxiliary variables at constant-factor cost without hindering unit propagation.)
2. A family of consistency checkers has polynomial-size CNF decompositions if and only if it has polynomial-size monotone circuits.
3. Consequently, if a family of domain consistency propagators has polynomial-size CNF decompositions, then the induced checkers, which decide whether the constraint has a solution in the current domain, have polynomial-size monotone circuits.

## Depends on

- [CNF decompositions of propagators and consistency checkers](cnf-decomposition-of-a-propagator.md): the objects being compared and the induced checker.
- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md): circuits with AND and OR gates only.

## Proof depends on

- [Tseitin clauses for a conjunction](../../../Logic/propositional-logic/tseitin-transformation/and-clauses.md): the three clauses per AND gate used for circuits to clauses.
- [Tseitin clauses for a disjunction](../../../Logic/propositional-logic/tseitin-transformation/or-clauses.md): the three clauses per OR gate.

## Expansion

*Item 1* (source Theorem 1, forward direction). For each variable $p$ of $C_P$ introduce $p_t$, $p_f$ with $p\to p_t$ and $\neg p\to p_f$; replace each clause by the implications simulating its unit propagation on the $p_t,p_f$ (for $(p\vee q\vee\neg r)$: $p_f\wedge q_f\to r_f$, $p_f\wedge r_t\to q_t$, $q_f\wedge r_t\to p_t$); add $p_t\wedge p_f\to\neg z$. Unit propagation on the copy never fails, and $z$ becomes false exactly when unit propagation on $C_P$ would produce the empty clause, i.e. when $f_P(\mathbf D)=\emptyset$. If $C_P$ already contains the empty clause, $f_P$ always returns $\emptyset$ and the checker decomposition is the single clause $\neg z$.

*Item 2, circuits to clauses* (source Lemma 1 and Corollary 1). The Tseitin clauses of a monotone circuit (one variable per gate, three clauses per AND or OR gate, a unit clause for each constant) form a CNF decomposition of the checker it computes: for a partial instantiation $I$ of the inputs and the input vector $b_i=0$ iff $\neg x_i\in I$, unit propagation forces the output to false iff the circuit outputs 0 on $b$. Monotonicity is what makes unset inputs behave as 1; the source's Example 3 shows this fails for non-monotone circuits.

*Item 2, clauses to circuits* (source Lemmas 2–4, Corollaries 2–3). Obligations not expanded here: (i) clauses containing a negative input literal can be removed without changing what unit propagation derives for $z$; (ii) along failure derivations, auxiliary variables can be renamed so that unit propagation only sets them to false, after which every clause relevant to deriving $\neg z$ has exactly one negative literal; (iii) a layered monotone circuit, with one OR gate per clause and one AND gate per auxiliary variable and for $z$ in each layer, computes after layer $i$ which of these variables are forced false within $i$ breadth-first rounds of unit propagation. Since $z$ is not among the auxiliary variables, $|\mathbf y|+1$ layers are needed (for example $(\neg y)\wedge(y\vee\neg z)$ has $|\mathbf y|=1$ and forces $z$ false in the second round), giving size $O((|\mathbf y|+1)\cdot|C_C|)$; the source uses $|\mathbf y|$ layers and writes $O(n|C_C|)$.

*Item 3* combines items 1 and 2. The source also states the converse, converting a checker decomposition back into a propagator decomposition by simulating the failed-literal test; that conversion is not included here, since for a checker that is not exact the map it realizes is not necessarily idempotent, and its size must also account for the direct-encoding clauses.

## Sources

- C. Bessiere, G. Katsirelos, N. Narodytska and T. Walsh, "Circuit complexity and decompositions of global constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 412–417, [https://www.ijcai.org/proceedings/2009/76](https://www.ijcai.org/proceedings/2009/76). Theorem 1 with its footnote on 3-CNF, Theorem 2 (CNF decompositions versus monotone circuits), the Tseitin encoding (Definition 6), Example 3, and Lemmas 1–4 and Corollaries 1–3 of §4 with their proofs (numbering of the IJCAI version), arXiv:0905.3757v1, [https://arxiv.org/abs/0905.3757v1](https://arxiv.org/abs/0905.3757v1).
