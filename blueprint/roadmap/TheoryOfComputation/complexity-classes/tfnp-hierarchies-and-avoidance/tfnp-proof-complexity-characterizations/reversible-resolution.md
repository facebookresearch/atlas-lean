# Reversible Resolution: a MaxSAT-style fragment of Resolution with consumed premises

A **Reversible Resolution (RevRes)** refutation of a CNF $F$ manipulates a multiset of clauses. It starts from a multiset of clauses of $F$, each with a freely chosen multiplicity. The only rules are the symmetric resolution rule and its inverse,

$$
C\lor x,\ C\lor\overline x\ \vdash\ C\qquad\text{and}\qquad C\ \vdash\ C\lor x,\ C\lor\overline x ,
$$

and each application **consumes** its premises: one occurrence of each premise is removed from the multiset and the conclusions are added. The refutation ends once an empty clause has been produced. Size and width are measured as for Resolution. RevRes is a sound restriction of Resolution, closely related to the MaxSAT resolution systems used by MaxSAT solvers, and it is $p$-simulated by unary Sherali–Adams, since the standard simulation of Resolution by Sherali–Adams applied to a RevRes proof yields coefficients bounded by the proof size. **RevResT** (Reversible Resolution with terminals) is a variant that additionally allows designated terminal clauses; it characterizes EOPL.

## Depends on

- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Resolution refutation](../../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../../Logic/propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
