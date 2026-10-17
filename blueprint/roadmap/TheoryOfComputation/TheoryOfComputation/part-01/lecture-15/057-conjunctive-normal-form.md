---
article_id: af_68f4ffc769a538cec64d181e
declaration: def
origin: cited
statement: formalized
lean: NPCompleteness.BoolFormula.IsCNF
---

# Definition (Conjunctive Normal Form)

A Boolean formula $\phi$ is in Conjunctive Normal Form (CNF) if it has the form $\phi = (x \lor \overline{y} \lor z) \land (\overline{x} \lor \overline{s} \lor z \lor u) \land \cdots \land (\overline{z} \lor \overline{u})$, where a literal is a variable or a negated variable, a clause is an OR ($\lor$) of literals, and a CNF is an AND ($\land$) of clauses. A 3CNF is a CNF with exactly 3 literals in each clause.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 15, $\leq_P$ Example: 3SAT and CLIQUE](../../../../../sources/v1/TheoryOfComputation.md)
