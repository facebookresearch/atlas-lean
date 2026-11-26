# Quantified constraint satisfaction QCSP(Γ) over a finite constraint language

Let $\Gamma$ be a finite set of relations on a finite set $D$. An instance of $\mathrm{QCSP}(\Gamma)$ is a sentence

$$
Q_1x_1\,Q_2x_2\cdots Q_nx_n\ \bigwedge_{j=1}^{s}R_j(x_{j,1},\dots,x_{j,r_j}),\qquad Q_i\in\{\forall,\exists\},\ R_j\in\Gamma,
$$

and the question is whether it is true in $(D;\Gamma)$. $\mathrm{QCSP}(\Gamma)\in\mathsf{PSPACE}$ by recursive evaluation of the quantifier prefix, and it can be PSPACE-complete (quantified 3-SAT is $\mathrm{QCSP}$ of the Boolean 3-clause relations). Its complexity is governed by the polymorphism clone $\mathrm{Pol}(\Gamma)$ through surjective polymorphisms, and one usually assumes $\Gamma$ contains all constants $\{d\}$, $d\in D$, so that $\mathrm{Pol}(\Gamma)$ is idempotent. Adding to $D$ a new isolated element that appears in no relation shows that $\mathrm{CSP}(\Gamma)$ and $\mathrm{QCSP}(\Gamma+1)$ are polynomially equivalent, so the QCSP classification contains the CSP classification.

## Depends on

- [Finite relational templates and the homomorphism problem CSP(A)](../finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md)
- [Polynomial space on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/pspace.md)
- [TQBF is PSPACE-complete](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)

## Sources

- Dmitriy Zhuk and Barnaby Martin, "QCSP Monsters and the Demise of the Chen Conjecture", STOC (2020); Journal of the ACM 69(5) (2022).
