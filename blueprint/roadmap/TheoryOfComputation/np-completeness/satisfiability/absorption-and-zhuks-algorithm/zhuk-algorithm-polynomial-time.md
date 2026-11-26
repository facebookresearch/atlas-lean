# Zhuk's algorithm solves CSP(A) in polynomial time whenever A has a WNU polymorphism

Let $\Gamma$ be a finite set of relations on a finite set $A$ containing all singleton unary relations and preserved by an idempotent WNU $w$ of arity $m$. Zhuk's recursive algorithm decides $\mathrm{CSP}(\Gamma)$ in polynomial time. On an instance $\Theta$ it: (1) enforces cycle-consistency; (2) enforces irreducibility; (3) replaces constraints by all weaker constraints and, recursively, shrinks each $D_i$ to the values extendable to solutions of the weakened instance; (4) shrinks a domain to a proper binary absorbing subuniverse, or (5) to a proper center, if one exists; (6) shrinks to a class of a congruence with PC quotient if one exists; (7) otherwise every domain $D_i$ with $|D_i| > 1$ has a proper congruence $\sigma_i$ with $(D_i;w)/\sigma_i$ linear, and the algorithm forms the factor instance $\Theta_L$, a system of linear equations over the fields $\mathbb{Z}_p$, solves it, and iteratively adds linear equations learned from recursive calls on instances with smaller domains until either a solution of $\Theta$ is found or $\Theta$ is shown unsatisfiable. Each recursive call strictly decreases some domain, so the recursion depth is bounded by a function of $|A|$, and the running time is polynomial in the instance size for fixed $\Gamma$.

## Proof sketch

Steps (1)-(3) only remove values that lie in no solution. Steps (4)-(6) are justified by the reduction lemmas for absorbing subuniverses, centers and PC congruence classes, and the four-types theorem shows that when none applies every nontrivial domain has a linear quotient. In the linear case Zhuk proves the existence of "bridges": if the factor solution does not lift, there is a constraint whose extension by a new $\mathbb{Z}_p$-valued variable defines one new linear equation, learnable from polynomially many recursive calls; the affine solution space shrinks in dimension each time, so at most $\sum_i\log_2|D_i|$ rounds occur.

## Depends on

- [Zhuk: reducing a domain to a binary absorbing subuniverse or a center preserves solvability](zhuk-reduction-to-absorbing-or-center.md)
- [Zhuk: reducing to a class of a congruence with polynomially complete quotient preserves solvability](zhuk-reduction-to-pc-congruence-class.md)
- [Zhuk's four-types theorem: binary absorption, center, polynomially complete quotient or affine quotient](zhuk-four-types-theorem.md)

## Proof depends on

- [Zhuk: reducing a domain to a binary absorbing subuniverse or a center preserves solvability](zhuk-reduction-to-absorbing-or-center.md)
- [Zhuk: reducing to a class of a congruence with polynomially complete quotient preserves solvability](zhuk-reduction-to-pc-congruence-class.md)
- [Zhuk's four-types theorem: binary absorption, center, polynomially complete quotient or affine quotient](zhuk-four-types-theorem.md)
- [Cycle-consistent, linked and irreducible CSP instances](cycle-consistent-linked-irreducible-instances.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
- Dmitriy Zhuk, "A simplified proof of the CSP Dichotomy Conjecture and XY-symmetric operations", arXiv preprint (2024), arXiv:2404.01080.
