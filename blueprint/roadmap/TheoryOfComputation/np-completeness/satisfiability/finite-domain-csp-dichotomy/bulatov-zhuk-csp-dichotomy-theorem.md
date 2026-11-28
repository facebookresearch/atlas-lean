# Bulatov and Zhuk: the CSP dichotomy theorem for finite templates

Let $\mathbb{A}$ be a finite relational structure with finite signature and let $\mathbb{C}$ be its core. Then exactly one of the following holds (assuming $\mathsf{P}\ne\mathsf{NP}$):

1. $\mathbb{C}$ has a WNU polymorphism (equivalently a Siggers polymorphism; equivalently $\mathbb{A}$ itself has a WNU polymorphism), and $\mathrm{CSP}(\mathbb{A})\in\mathsf{P}$;
2. otherwise, $\mathrm{CSP}(\mathbb{A})$ is NP-complete.

In particular the Feder–Vardi Dichotomy Conjecture and the Algebraic Dichotomy Conjecture are true. Hardness is the Bulatov–Jeavons–Krokhin theorem combined with Maróti–McKenzie; tractability was proved independently by Bulatov (via congruence separation, centralizers and a "few subpowers"/bounded-width decomposition) and by Zhuk (via binary absorbing subuniverses, centers, and congruences with polynomially complete or linear quotients, and a recursive domain-reduction algorithm).

## Proof sketch

For the hardness side, the absence of a WNU polymorphism of the core yields no Taylor polymorphism of $\mathbb{C}^c$, so NP-hardness follows from BJK. For tractability one may pass to $\mathbb{C}^c$ with an idempotent WNU $w$; Zhuk's algorithm makes the instance cycle-consistent and irreducible, then repeatedly shrinks a domain to a binary absorbing subuniverse, a center, or a class of a polynomially complete quotient (which provably preserves satisfiability), and when none applies every domain has a linear quotient, where the remaining instance is handled by solving linear equations over $\mathbb{Z}_p$ and adding learned equations. The height-1 nature of the WNU identities makes the condition invariant between $\mathbb{A}$ and its core.

## Depends on

- [The Feder–Vardi Dichotomy Conjecture and its algebraic form](feder-vardi-dichotomy-conjecture.md)
- [Cores of finite relational structures](cores-of-finite-relational-structures.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](wnu-taylor-siggers-cyclic-operations.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Finite relational templates and the homomorphism problem CSP(A)](finite-templates-and-csp-of-a.md)

## Proof depends on

- [Bulatov–Jeavons–Krokhin: a core with no Taylor polymorphism has an NP-complete CSP](bulatov-jeavons-krokhin-no-taylor-np-complete.md)
- [Maróti–McKenzie: finite Taylor algebras have weak near-unanimity terms](maroti-mckenzie-taylor-implies-wnu.md)
- [Siggers: a finite algebra is Taylor iff it has a 6-ary Siggers term](siggers-six-ary-taylor-term.md)
- [Every finite structure has a unique core, and constants can be added to a core without changing CSP complexity](core-uniqueness-and-adding-constants.md)
- [Barto–Opršal–Pinsker: pp-constructibility is captured by minion homomorphisms of polymorphisms](barto-oprsal-pinsker-pp-constructions-minion-homomorphisms.md)

## Sources

- Andrei A. Bulatov, "A Dichotomy Theorem for Nonuniform CSPs", FOCS (2017), arXiv:1703.03021.
- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
