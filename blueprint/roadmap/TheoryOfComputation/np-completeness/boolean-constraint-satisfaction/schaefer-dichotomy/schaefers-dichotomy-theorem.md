# Schaefer's dichotomy theorem

Let $\Gamma$ be a finite Boolean constraint language. If $\Gamma$ satisfies Schaefer's criterion then $\mathrm{CSP}(\Gamma)$ is decidable in polynomial time; otherwise $\mathrm{CSP}(\Gamma)$ is NP-complete. The tractable cases are solved by the constant assignments, Horn and dual-Horn satisfiability, 2-SAT and Gaussian elimination over $\mathbb{F}_2$ respectively.

## Proof sketch

Tractability uses the normal forms of each class (Horn, dual Horn, 2-CNF, affine systems). For hardness, by the lemma all polymorphisms are projections, which preserve the 1-in-3 relation, or projections and negated projections, which preserve the NAE-3 relation (the self-dual case); by the Galois connection these relations are pp-definable from $\Gamma$, so 1-in-3-SAT or NAE-3-SAT reduces to $\mathrm{CSP}(\Gamma)$ by gadget replacement.

## Depends on

- [Schaefer's six tractable classes](schaefers-six-tractable-classes.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Without Schaefer polymorphisms, all polymorphisms are projections or negated projections](without-schaefer-polymorphisms.md)
- [Pol–Inv Galois connection over finite domains: CSP complexity depends only on the polymorphism clone](../../satisfiability/finite-domain-csp-dichotomy/pol-inv-galois-connection-finite-domains.md)
- [Horn-definable relations are exactly the AND-closed relations](../polymorphisms-of-boolean-relations/horn-definable-iff-and-closed.md)
- [2-CNF-definable relations are exactly the majority-closed relations](../polymorphisms-of-boolean-relations/two-cnf-definable-iff-majority-closed.md)
- [Affine relations are exactly the minority-closed relations](../polymorphisms-of-boolean-relations/affine-iff-minority-closed.md)
- [Correctness of the Horn satisfiability test](../../../../Logic/propositional-logic/horn-satisfiability/horn-sat-eq-true-iff.md)
- [2-SAT characterization](../../../../Logic/propositional-logic/2-satisfiability/cnf-sat-iff-of-is-two-cnf.md)
- [1-IN-3-SAT is NP-complete](../../satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)
- [NOT-ALL-EQUAL 3-SAT is NP-complete](../../satisfiability/not-all-equal-3-sat/nae-three-sat-np-complete.md)

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Theorem 3.20.
