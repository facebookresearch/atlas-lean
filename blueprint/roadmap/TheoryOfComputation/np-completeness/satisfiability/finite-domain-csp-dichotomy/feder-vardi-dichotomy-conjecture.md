# The Feder–Vardi Dichotomy Conjecture and its algebraic form

The **Feder–Vardi Dichotomy Conjecture** (1993, published 1998) asserts: for every finite relational structure $\mathbb{A}$, the problem $\mathrm{CSP}(\mathbb{A})$ is either in $\mathsf{P}$ or NP-complete. Feder and Vardi motivated it by showing that every problem in the logic class MMSNP (monotone monadic SNP) is equivalent, under randomized polynomial-time reductions, to a finite union of finite-template CSPs (Kun derandomized these reductions), whereas Ladner's theorem rules out such a dichotomy for all of $\mathsf{NP}$ unless $\mathsf{P}=\mathsf{NP}$. The **Algebraic Dichotomy Conjecture** (Bulatov–Jeavons–Krokhin) sharpens it: for a finite core $\mathbb{C}$, $\mathrm{CSP}(\mathbb{C})\in\mathsf{P}$ if $\mathbb{C}^c$ has a Taylor polymorphism, and NP-complete otherwise. Both statements were posed as conjectures; they were settled in 2017 (see the dichotomy theorem in this folder).

## Depends on

- [Finite relational templates and the homomorphism problem CSP(A)](finite-templates-and-csp-of-a.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](wnu-taylor-siggers-cyclic-operations.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Tomás Feder and Moshe Y. Vardi, "The Computational Structure of Monotone Monadic SNP and Constraint Satisfaction: A Study through Datalog and Group Theory", SIAM Journal on Computing 28(1) (1998).
- Gábor Kun, "Constraints, MMSNP and expander relational structures", Combinatorica 33(3) (2013), arXiv:0706.1701.
- Andrei Bulatov, Peter Jeavons and Andrei Krokhin, "Classifying the Complexity of Constraints Using Finite Algebras", SIAM Journal on Computing 34(3) (2005).
