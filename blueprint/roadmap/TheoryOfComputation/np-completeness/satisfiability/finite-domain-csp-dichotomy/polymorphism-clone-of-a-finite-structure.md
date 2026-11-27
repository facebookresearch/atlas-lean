# Polymorphisms of a finite structure and its polymorphism clone Pol(A)

Let $\mathbb{A}$ be a finite $\tau$-structure. An $n$-ary operation $f:A^n\to A$ is a **polymorphism** of $\mathbb{A}$ if for every $R\in\tau$ of arity $r$ and all tuples $\bar a^1,\dots,\bar a^n\in R^{\mathbb{A}}$, the tuple obtained by applying $f$ coordinatewise,

$$
\bigl(f(a^1_1,\dots,a^n_1),\dots,f(a^1_r,\dots,a^n_r)\bigr),
$$

again lies in $R^{\mathbb{A}}$; equivalently, $f$ is a homomorphism $\mathbb{A}^n\to\mathbb{A}$ from the $n$-th categorical power. The set $\mathrm{Pol}(\mathbb{A})$ of all polymorphisms of all arities contains every projection $\pi^n_i(x_1,\dots,x_n)=x_i$ and is closed under composition, hence is a **clone**. A polymorphism $f$ is **idempotent** if $f(x,\dots,x)=x$; unary polymorphisms are the endomorphisms of $\mathbb{A}$. A relation $S\subseteq A^m$ is **primitive-positive (pp) definable** in $\mathbb{A}$ if $S=\{\bar x:\exists \bar y\,\psi(\bar x,\bar y)\}$ for a conjunction $\psi$ of atomic formulas over $\tau$ and equalities. Over arbitrary finite domains (not only the two-element one), every polymorphism of $\mathbb{A}$ preserves every pp-definable relation.

## Depends on

- [Finite relational templates and the homomorphism problem CSP(A)](finite-templates-and-csp-of-a.md)

## Sources

- Andrei Bulatov, Peter Jeavons and Andrei Krokhin, "Classifying the Complexity of Constraints Using Finite Algebras", SIAM Journal on Computing 34(3) (2005).
- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
