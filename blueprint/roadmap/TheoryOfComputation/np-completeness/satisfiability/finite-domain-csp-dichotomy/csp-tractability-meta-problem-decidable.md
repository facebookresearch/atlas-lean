# The CSP tractability meta-problem is decidable via a single height-1 Siggers check

There is an algorithm that, given a finite relational structure $\mathbb{A}$ (finite signature), decides whether $\mathrm{CSP}(\mathbb{A})$ is in $\mathsf{P}$ or NP-complete (under $\mathsf{P}\ne\mathsf{NP}$): it decides whether $\mathbb{A}$ has a 6-ary polymorphism $s$ with $s(x,y,x,z,y,z)=s(y,x,z,x,z,y)$ for all $x,y,z\in A$, by exhaustive search over the at most $|A|^{|A|^6}$ six-ary operations, checking for each relation $R$ of arity $r$ that $s$ maps $(R^{\mathbb{A}})^6$ into $R^{\mathbb{A}}$. No computation of the core is needed.

## Proof sketch

$\mathbb{A}$ and its core $\mathbb{C}$ are homomorphically equivalent, so composing with the maps $\mathbb{A}\to\mathbb{C}\to\mathbb{A}$ gives minion homomorphisms in both directions between $\mathrm{Pol}(\mathbb{A})$ and $\mathrm{Pol}(\mathbb{C})$, and the Siggers identity is of height 1. If $\mathbb{C}$ has a Siggers polymorphism $s$, then $s(x,\dots,x)$ is an automorphism $\alpha$ and $\alpha^{-1}\circ s$ is an idempotent Siggers, hence Taylor, polymorphism of $\mathbb{C}^c$; conversely Taylor implies Siggers by Siggers' theorem. The dichotomy theorem then identifies the two cases.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Finite relational templates and the homomorphism problem CSP(A)](finite-templates-and-csp-of-a.md)

## Proof depends on

- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](bulatov-zhuk-csp-dichotomy-theorem.md)
- [Siggers: a finite algebra is Taylor iff it has a 6-ary Siggers term](siggers-six-ary-taylor-term.md)
- [Barto–Opršal–Pinsker: pp-constructibility is captured by minion homomorphisms of polymorphisms](barto-oprsal-pinsker-pp-constructions-minion-homomorphisms.md)
- [Every finite structure has a unique core, and constants can be added to a core without changing CSP complexity](core-uniqueness-and-adding-constants.md)

## Sources

- Mark H. Siggers, "A strong Mal'cev condition for locally finite varieties omitting the unary type", Algebra Universalis 64 (2010).
- Libor Barto, Jakub Opršal and Michael Pinsker, "The wonderland of reflections", Israel Journal of Mathematics 223 (2018), arXiv:1510.04521.
- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
