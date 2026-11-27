# Zhuk: reducing a domain to a binary absorbing subuniverse or a center preserves solvability

Let $\Theta$ be a CSP instance over a constraint language preserved by a special WNU $w$, with each domain $D_j$ a subuniverse of $(A;w)$, and suppose $\Theta$ is cycle-consistent and irreducible. If $B\subsetneq D_i$ is a nonempty proper binary absorbing subuniverse or a nonempty proper center of $(D_i;w)$, then $\Theta$ has a solution if and only if $\Theta$ has a solution with $x_i\in B$ (Zhuk, Theorem 5.5).

## Proof sketch

Assume solutions exist but none lies in $B$; choose a minimal "crucial" subinstance witnessing this. Absorption propagates along constraints: the set of values reachable from $B$ through a subdirect constraint is again absorbing (binary absorption or centrality transfers through pp-definitions), and cycle-consistency plus irreducibility force these propagated sets to be compatible across the instance so that a contradiction is reached without requiring any extra weaker-instance consistency hypothesis.

## Depends on

- [Cycle-consistent, linked and irreducible CSP instances](cycle-consistent-linked-irreducible-instances.md)
- [Zhuk's centers, polynomially complete algebras and linear quotients](zhuk-centers-polynomially-complete-linear-algebras.md)
- [Absorbing and binary absorbing subuniverses of a finite algebra](absorbing-and-binary-absorbing-subuniverses.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](../finite-domain-csp-dichotomy/wnu-taylor-siggers-cyclic-operations.md)

## Proof depends on

- [Barto–Kozik Absorption Theorem for linked subdirect products of Taylor algebras](barto-kozik-absorption-theorem.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
