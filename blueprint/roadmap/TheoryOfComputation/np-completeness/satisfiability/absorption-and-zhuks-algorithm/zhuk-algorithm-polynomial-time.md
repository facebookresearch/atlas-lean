# Zhuk's algorithm solves CSP(A) in polynomial time whenever A has a WNU polymorphism

Let $\Gamma$ be a finite set of relations on a finite set $A$ containing all singleton unary relations and preserved by an idempotent WNU, and fix a **special WNU** $w$ of arity $m$ in its polymorphism clone (which always exists for a finite idempotent algebra with a WNU). Zhuk's recursive algorithm decides $\mathrm{CSP}(\Gamma)$ in polynomial time, working throughout with the algebra $(A;w)$ and its subuniverses. On an instance $\Theta$ it: (1) enforces cycle-consistency; (2) enforces irreducibility; (3) replaces constraints by all weaker constraints and, recursively, shrinks each $D_i$ to the values extendable to solutions of the weakened instance; (4) shrinks a domain to a proper binary absorbing subuniverse of $(D_i;w)$, or (5) to a proper center of $(D_i;w)$, if one exists; (6) shrinks to a class of a congruence with PC quotient if one exists; (7) otherwise every domain $D_i$ with $|D_i| > 1$ has a proper congruence $\sigma_i$ with $(D_i;w)/\sigma_i$ linear, and the algorithm forms the factor instance $\Theta_L$, a system of linear equations over the fields $\mathbb{Z}_p$, solves it, and iteratively adds linear equations learned from recursive calls on instances with smaller domains until either a solution of $\Theta$ is found or $\Theta$ is shown unsatisfiable. Not every recursive call shrinks a domain: the calls of step (3) (CheckWeakerInstance) keep the domains and instead make every constraint relation strictly smaller in a fixed partial order on the finitely many relations of $\Gamma$ (smaller arity; or equal arity with smaller coordinate projections; or equal projections and a larger relation). All other recursive calls reduce every domain of size greater than $1$ and never enlarge one. Hence the recursion depth is less than $|A|+|\Gamma|$ (Zhuk, Lemma 5.2), a constant for the fixed language, and the running time is polynomial in the instance size for fixed $\Gamma$.

## Proof sketch

Steps (1)-(3) only remove values that lie in no solution. Steps (4)-(6) are justified by the reduction lemmas for absorbing subuniverses, centers and PC congruence classes, and the four-types theorem shows that when none applies every nontrivial domain has a linear quotient. In the linear case Zhuk proves the existence of "bridges": if the factor solution does not lift, there is a constraint whose extension by a new $\mathbb{Z}_p$-valued variable defines one new linear equation, learnable from polynomially many recursive calls; the affine solution space shrinks in dimension each time, so at most $\sum_i\log_2|D_i|$ rounds occur.

## Depends on

- [Cycle-consistent, linked and irreducible CSP instances](cycle-consistent-linked-irreducible-instances.md)
- [Absorbing and binary absorbing subuniverses of a finite algebra](absorbing-and-binary-absorbing-subuniverses.md)
- [Zhuk's centers, polynomially complete algebras and linear quotients](zhuk-centers-polynomially-complete-linear-algebras.md)

## Proof depends on

- [Zhuk: reducing a domain to a binary absorbing subuniverse or a center preserves solvability](zhuk-reduction-to-absorbing-or-center.md)
- [Zhuk: reducing to a class of a congruence with polynomially complete quotient preserves solvability](zhuk-reduction-to-pc-congruence-class.md)
- [Zhuk's four-types theorem: binary absorption, center, polynomially complete quotient or affine quotient](zhuk-four-types-theorem.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM 67(5) (2020), doi:10.1145/3402029; arXiv:1704.01914 (Lemma 5.2).
