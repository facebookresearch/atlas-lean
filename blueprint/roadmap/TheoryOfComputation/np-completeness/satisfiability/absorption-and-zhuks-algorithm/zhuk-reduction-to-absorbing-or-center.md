# Zhuk: reducing a domain to a binary absorbing subuniverse or a center preserves solvability

Let $\Theta$ be a CSP instance over a constraint language preserved by an idempotent WNU $w$, with each domain $D_j$ a subuniverse, and suppose $\Theta$ is cycle-consistent and irreducible and satisfies the additional consistency condition maintained by Zhuk's algorithm (for every $i$ and $b\in D_i$, the instance obtained by replacing every constraint by all its weaker constraints has a solution with $x_i=b$). If $B\subsetneq D_i$ is a proper binary absorbing subuniverse or a proper center of $(D_i;w)$, then: if $\Theta$ has a solution, it has a solution with $x_i\in B$.

## Proof sketch

Assume solutions exist but none lies in $B$; choose a minimal "crucial" subinstance witnessing this. Absorption propagates along constraints: the set of values reachable from $B$ through a subdirect constraint is again absorbing (binary absorption or centrality transfers through pp-definitions), and cycle-consistency plus irreducibility force these propagated sets to be compatible across the instance. One then builds, from a solution of the weakened instance with $x_i\in B$ and a genuine solution, a solution with $x_i\in B$ by applying the absorbing term coordinatewise.

## Depends on

- [Cycle-consistent, linked and irreducible CSP instances](cycle-consistent-linked-irreducible-instances.md)
- [Zhuk's centers, polynomially complete algebras and linear quotients](zhuk-centers-polynomially-complete-linear-algebras.md)
- [Absorbing and binary absorbing subuniverses of a finite algebra](absorbing-and-binary-absorbing-subuniverses.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](../finite-domain-csp-dichotomy/wnu-taylor-siggers-cyclic-operations.md)

## Proof depends on

- [Barto–Kozik Absorption Theorem for linked subdirect products of Taylor algebras](barto-kozik-absorption-theorem.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
