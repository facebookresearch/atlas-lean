# Deterministic Nelson–Oppen combination for convex theories

Let $T_1$ and $T_2$ be signature-disjoint first-order theories that are [convex with respect to equations](convex-theories.md) and have no trivial models, and let $F_1$ and $F_2$ be pure conjunctions of literals over $T_1$ and $T_2$. Assume that decision procedures for the $T_i$-satisfiability of existentially quantified conjunctions of literals are given; the rules below call them, for Unsat directly and for the entailment tests of Propagate through the unsatisfiability of $F_i \wedge x \not\approx y$. The deterministic Nelson–Oppen procedure applies two rules to the pair $(F_1, F_2)$:

- **Unsat:** stop with $\bot$ if $\exists \vec x\, F_i$ is unsatisfiable with respect to $T_i$ for some $i$;
- **Propagate:** replace $(F_1, F_2)$ by $(F_1 \wedge x \approx y, F_2 \wedge x \approx y)$ if $x$ and $y$ are distinct variables occurring in both $F_1$ and $F_2$ such that $T_i \models \forall \vec x\,(F_i \to x \approx y)$ holds for exactly one $i \in \{1, 2\}$.

Relative to these procedures, it terminates and is sound and complete for deciding satisfiability of $F_1 \wedge F_2$ with respect to $T_1 \cup T_2$; with effective component procedures it is a decision procedure. It needs $O(n^3)$ calls to the component procedures, where $n$ is the number of shared variables.

**Proof.** Only finitely many equations can be added, and each is entailed. In an irreducible pair both $F_i$ entail the same equations between shared variables; by convexity each $F_i$ is satisfiable together with the arrangement that makes exactly these equations true. Both theories are stably infinite, so the Nelson–Oppen combination theorem gives a model of $F_1 \wedge F_2$.

## Depends on

- [Convex theories](convex-theories.md)
- [Purification into separate form](purification-into-separate-form.md)

## Proof depends on

- [Convex theories without trivial models are stably infinite](convex-theories-are-stably-infinite.md)
- [Nelson–Oppen combination of decision procedures](nelsonoppen-combination-of-decision-procedures.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.11, Lemma 1.8, the deterministic version of the Nelson–Oppen algorithm, Theorem 1.9 with its proof and Corollary 1.10, pp. 29–30.
