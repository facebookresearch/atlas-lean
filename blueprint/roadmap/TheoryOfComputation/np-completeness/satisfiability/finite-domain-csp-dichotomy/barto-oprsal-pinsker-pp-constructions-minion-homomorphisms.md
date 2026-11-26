# Barto–Opršal–Pinsker: pp-constructibility is captured by minion homomorphisms of polymorphisms

Let $\mathbb{A}$ and $\mathbb{B}$ be finite relational structures. The following are equivalent:

1. $\mathbb{B}$ is pp-constructible from $\mathbb{A}$;
2. there exists a minion (h1 clone) homomorphism $\mathrm{Pol}(\mathbb{A})\to\mathrm{Pol}(\mathbb{B})$.

Moreover, if $\mathbb{B}$ is pp-constructible from $\mathbb{A}$ then $\mathrm{CSP}(\mathbb{B})$ reduces to $\mathrm{CSP}(\mathbb{A})$ in logarithmic space. Hence the complexity of $\mathrm{CSP}(\mathbb{A})$, up to log-space reductions, depends only on the height-1 identities satisfied by polymorphisms of $\mathbb{A}$. On the algebraic side the closure operator is "reflections, finite products and expansions", an analogue of Birkhoff's HSP theorem for height-1 identities.

## Proof sketch

Pp-powers correspond to finite powers of the polymorphism algebra and pp-definitions to subalgebras, while homomorphic equivalence corresponds to the new operation of taking a **reflection** (a "double shrink" of an algebra along maps $A\to B\to A$); minion homomorphisms preserve exactly the height-1 identities, which are those preserved by these three constructions. For the reduction, a pp-power instance is expanded by substituting pp-definitions coordinatewise, and homomorphically equivalent templates have identical CSPs.

## Depends on

- [Minions, minion homomorphisms and pp-constructions](minions-minion-homomorphisms-pp-constructions.md)
- [Log-space many-one reductions](../../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)

## Proof depends on

- [Pol–Inv Galois connection over finite domains: CSP complexity depends only on the polymorphism clone](pol-inv-galois-connection-finite-domains.md)
- [Every finite structure has a unique core, and constants can be added to a core without changing CSP complexity](core-uniqueness-and-adding-constants.md)

## Sources

- Libor Barto, Jakub Opršal and Michael Pinsker, "The wonderland of reflections", Israel Journal of Mathematics 223 (2018), arXiv:1510.04521.
