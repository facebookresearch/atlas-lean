# Schaefer's dichotomy theorem for Boolean CSPs

For every finite Boolean constraint language $\Gamma$: if $\Gamma$ is preserved by one of the polymorphisms constant $0$, constant $1$, AND, OR, majority, or parity, then $\mathrm{CSP}(\Gamma)$ is in $\mathsf{P}$ (respectively: trivially satisfiable, Horn, dual-Horn, 2-SAT, affine over $\mathbb{F}_2$); otherwise $\mathrm{CSP}(\Gamma)$ is $\mathsf{NP}$-complete. In particular every Boolean CSP is either in $\mathsf{P}$ or $\mathsf{NP}$-complete.

## Proof sketch

Tractable cases: each polymorphism class yields a known algorithm (constant assignment, unit propagation for Horn/dual-Horn, implication graphs for bijunctive relations, Gaussian elimination for affine ones). Hardness: if none of the six polymorphisms is present, the relations of $\Gamma$ pp-define (with constants obtained from the absence of constant polymorphisms, possibly after a self-dual lift) a relation encoding 3-SAT clauses, giving a reduction from 3-SAT.

## Depends on

- [Boolean constraint languages and polymorphisms](boolean-constraint-languages.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Correctness of the Horn satisfiability test](../../../Logic/propositional-logic/horn-satisfiability/horn-sat-eq-true-iff.md)
- [2-SAT witnesses in polynomial time via the implication graph](../../polynomial-time-problems/two-sat-and-xor-sat-algorithms/two-sat-witness-construction.md)
- [XOR-SAT is solvable by Gaussian elimination over GF(2)](../../polynomial-time-problems/two-sat-and-xor-sat-algorithms/xor-sat-gaussian-elimination.md)
- [Cook–Levin theorem: SAT is NP-complete](../cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Thomas J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th Annual ACM Symposium on Theory of Computing, 1978.
- Hubie Chen, "A Rendezvous of Logic, Complexity, and Algebra", arXiv:cs/0611018, 2006, Theorem 4.3.
