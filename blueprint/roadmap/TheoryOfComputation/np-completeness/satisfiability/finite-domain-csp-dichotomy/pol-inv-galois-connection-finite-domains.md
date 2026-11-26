# Pol–Inv Galois connection over finite domains: CSP complexity depends only on the polymorphism clone

Let $\mathbb{A}$ be a finite structure and $S\subseteq A^m$. Then $S$ is pp-definable in $\mathbb{A}$ if and only if $S$ is preserved by every polymorphism of $\mathbb{A}$ (the finite-domain Galois correspondence $\mathrm{Inv}(\mathrm{Pol}(\mathbb{A}))=\langle\mathbb{A}\rangle_{pp}$). Consequently, if $\mathbb{A}$ and $\mathbb{B}$ have the same domain and $\mathrm{Pol}(\mathbb{A})\subseteq\mathrm{Pol}(\mathbb{B})$, then every relation of $\mathbb{B}$ is pp-definable in $\mathbb{A}$, and $\mathrm{CSP}(\mathbb{B})$ reduces to $\mathrm{CSP}(\mathbb{A})$ by a log-space reduction that replaces each atom by its pp-definition and introduces fresh existential variables. In particular two finite structures on the same domain with equal polymorphism clones have log-space equivalent CSPs.

## Proof sketch

Preservation of pp-definable relations is a direct check. Conversely, given $S$ preserved by $\mathrm{Pol}(\mathbb{A})$, list $S=\{\bar s^1,\dots,\bar s^n\}$ and consider the $|A|^n$-ary relation $\mathrm{Hom}(\mathbb{A}^n,\mathbb{A})$ viewed as a relation on $A^{A^n}$, which is pp-definable by the "canonical conjunctive query" of $\mathbb{A}^n$; projecting it onto the $m$ coordinates indexed by the rows of the matrix with columns $\bar s^i$ yields exactly $\{f(\bar s^1,\dots,\bar s^n):f\in\mathrm{Pol}(\mathbb{A})\}$, which equals $S$ because $S$ is closed under polymorphisms and contains each $\bar s^i$ (via projections). The reduction is local gadget substitution and is computable in logarithmic space.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Log-space many-one reductions](../../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Log-space many-one reductions](../../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Sources

- Andrei Bulatov, Peter Jeavons and Andrei Krokhin, "Classifying the Complexity of Constraints Using Finite Algebras", SIAM Journal on Computing 34(3) (2005).
- Libor Barto, Jakub Opršal and Michael Pinsker, "The wonderland of reflections", Israel Journal of Mathematics 223 (2018), arXiv:1510.04521.
