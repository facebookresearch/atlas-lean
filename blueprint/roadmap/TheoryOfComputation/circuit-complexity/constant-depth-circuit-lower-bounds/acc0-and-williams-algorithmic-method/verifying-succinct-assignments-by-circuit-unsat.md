# Verifying a succinct satisfying assignment by circuit unsatisfiability

Let $D$ be a circuit on $q$ inputs describing $2^q$ clauses of three literals over $2^r$ variables (each output block gives a variable address in $r$ bits and a sign), and let $W$ be a circuit on $r$ inputs describing an assignment $y\mapsto W(y)$. The circuit $\mathrm{Bad}_{D,W}(z)$ on $q$ inputs that tests whether the clause addressed by $z$ is falsified by $W$ uses one copy of $D$ and three copies of $W$; $W$ encodes a satisfying assignment of the succinct formula iff $\mathrm{Bad}_{D,W}$ is unsatisfiable. If $D$ and $W$ are $\mathsf{ACC}^0$ circuits, so is $\mathrm{Bad}_{D,W}$, with depth increased by a constant.

## Proof sketch

Plug the three address blocks of $D(z)$ into three copies of $W$ and compare with the signs; the clause is violated iff all three literals evaluate to false.

## Depends on

- [Straight-line programs and circuits over a basis](../../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Satisfiability of a CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- Ryan Williams, "Improving Exhaustive Search Implies Superpolynomial Lower Bounds", SIAM Journal on Computing 42(3), 2013 (STOC 2010).
- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Section 3, proof sketch of Theorem 3.1 and Lemma 3.1).
