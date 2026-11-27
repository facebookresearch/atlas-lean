# Zhuk: reducing to a class of a congruence with polynomially complete quotient preserves solvability

Let $\Theta$ be a cycle-consistent irreducible instance over a language preserved by a special WNU $w$ (an idempotent WNU with $x\circ(x\circ y)=x\circ y$ for $x\circ y=w(x,\dots,x,y)$; the clone of every idempotent WNU on a finite set contains one), such that no domain $D_j$ has a nonempty proper binary absorbing subuniverse or a nonempty proper center in $(D_j;w)$. Let $\sigma$ be a congruence of $(D_i;w)$ such that $(D_i;w)/\sigma$ is polynomially complete, and let $E$ be any $\sigma$-class. Then $\Theta$ has a solution if and only if $\Theta$ has a solution with $x_i\in E$.

## Proof sketch

Polynomial completeness of the quotient means every operation on $D_i/\sigma$ is a polynomial, so any relation linking the $\sigma$-classes in a subdirect way must be "rectangular" modulo $\sigma$ unless it induces a binary absorption or center somewhere, which is excluded. Hence, by irreducibility, the projection of the solution set onto $x_i$ is a union of $\sigma$-classes and is either empty or meets every class, in particular $E$.

## Depends on

- [Cycle-consistent, linked and irreducible CSP instances](cycle-consistent-linked-irreducible-instances.md)
- [Zhuk's centers, polynomially complete algebras and linear quotients](zhuk-centers-polynomially-complete-linear-algebras.md)
- [Absorbing and binary absorbing subuniverses of a finite algebra](absorbing-and-binary-absorbing-subuniverses.md)

## Proof depends on

- [Zhuk's four-types theorem: binary absorption, center, polynomially complete quotient or affine quotient](zhuk-four-types-theorem.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
