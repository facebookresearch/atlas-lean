# Every finite structure has a unique core, and constants can be added to a core without changing CSP complexity

Let $\mathbb{A}$ be a finite structure. (i) $\mathbb{A}$ has a core $\mathbb{C}$, unique up to isomorphism; $\mathbb{A}$ and $\mathbb{C}$ are homomorphically equivalent, hence $\mathrm{CSP}(\mathbb{A})=\mathrm{CSP}(\mathbb{C})$ as sets of instances. (ii) If $\mathbb{C}$ is a core with domain $C$, let $\mathbb{C}^{c}$ be its expansion by all singleton unary relations $\{a\}$, $a\in C$. Then $\mathrm{CSP}(\mathbb{C}^{c})$ reduces in polynomial time (indeed in log space) to $\mathrm{CSP}(\mathbb{C})$. Every polymorphism of $\mathbb{C}^{c}$ is idempotent, so for the purpose of classifying the complexity of $\mathrm{CSP}(\mathbb{A})$ one may assume that the template is a core whose polymorphism clone is idempotent (the **idempotent reduct**).

## Proof sketch

(i) Compose an endomorphism with minimal image with itself repeatedly to obtain a retraction onto a core; two cores homomorphically equivalent to $\mathbb{A}$ map into each other, and each composite is a bijective endomorphism of a core, so the cores are isomorphic. Homomorphic equivalence means $\mathbb{X}\to\mathbb{A}$ iff $\mathbb{X}\to\mathbb{C}$. (ii) Given an instance of $\mathrm{CSP}(\mathbb{C}^c)$, add a disjoint copy of $\mathbb{C}$ with a vertex $v_a$ for each $a$ and identify every variable constrained to $\{a\}$ with $v_a$; a homomorphism of the new instance to $\mathbb{C}$ restricts on the copy to an endomorphism, which is an automorphism $\alpha$, and composing with $\alpha^{-1}$ yields a solution respecting the constants.

## Depends on

- [Cores of finite relational structures](cores-of-finite-relational-structures.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Finite relational templates and the homomorphism problem CSP(A)](finite-templates-and-csp-of-a.md)

## Sources

- Andrei Bulatov, Peter Jeavons and Andrei Krokhin, "Classifying the Complexity of Constraints Using Finite Algebras", SIAM Journal on Computing 34(3) (2005).
- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
