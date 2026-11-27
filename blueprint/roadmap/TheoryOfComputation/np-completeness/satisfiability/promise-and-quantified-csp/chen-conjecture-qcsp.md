# The Chen Conjecture on the complexity of QCSP

The **Chen Conjecture** (Hubie Chen, "Meditations on Quantified Constraint Satisfaction", 2012) asserts: let $\Gamma$ be a finite constraint language on a finite set $D$ containing all constants. If the idempotent algebra $(D;\mathrm{Pol}(\Gamma))$ has PGP, then $\mathrm{QCSP}(\Gamma)\in\mathsf{NP}$; otherwise it has EGP and $\mathrm{QCSP}(\Gamma)$ is PSPACE-complete. Combined with the CSP dichotomy, the conjecture would have yielded a trichotomy: every such $\mathrm{QCSP}(\Gamma)$ is in $\mathsf{P}$, NP-complete or PSPACE-complete. The conjecture is stated here as a hypothesis; it turned out to be false (Zhuk–Martin).

## Depends on

- [Polynomially and exponentially generated powers (PGP and EGP)](polynomially-exponentially-generated-powers.md)
- [Quantified constraint satisfaction QCSP(Γ) over a finite constraint language](quantified-csp-over-finite-language.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Polynomial space on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/pspace.md)

## Sources

- Hubie Chen, "Meditations on Quantified Constraint Satisfaction", in Logic and Program Semantics, Lecture Notes in Computer Science 7230 (2012), arXiv:1201.6306.
- Dmitriy Zhuk and Barnaby Martin, "QCSP Monsters and the Demise of the Chen Conjecture", STOC (2020); Journal of the ACM 69(5) (2022).
