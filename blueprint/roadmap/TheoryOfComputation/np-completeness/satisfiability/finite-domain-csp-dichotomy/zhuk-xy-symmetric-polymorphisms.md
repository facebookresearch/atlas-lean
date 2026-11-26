# Zhuk: CSP tractability is equivalent to infinitely many polymorphisms symmetric on all two-element sets

Call an $n$-ary operation $f$ on $A$ **symmetric on all two-element sets** (XY-symmetric) if for all $x,y\in A$ and all $\bar u,\bar v\in\{x,y\}^n$ containing the same number of occurrences of $x$, we have $f(\bar u)=f(\bar v)$. Zhuk (2024) proves: if a finite set of relations $\Gamma$ on a finite set $A$ has a WNU polymorphism of odd arity $n$, then composing it one obtains an $n$-ary polymorphism of $\Gamma$ that is symmetric on all two-element sets. Consequently, $\mathrm{CSP}(\Gamma)$ is solvable in polynomial time if and only if $\Gamma$ has infinitely many polymorphisms that are symmetric on all two-element sets (and is NP-complete otherwise). The same paper gives a new, simplified proof of correctness of Zhuk's algorithm based on a globally defined theory of strong subuniverses and linear congruences.

## Proof sketch

The globally defined strong subuniverses (binary absorbing, central, PC-type and linear) satisfy an intersection property and factor through products; using them one shows that suitable compositions of an odd WNU can be repeatedly "fixed" on each two-element subset without destroying the property on the others, giving XY-symmetry. Conversely an XY-symmetric operation of arity at least 3 restricts to a WNU on its idempotent part, so infinitely many such polymorphisms imply a WNU polymorphism and tractability by the dichotomy theorem; Barto–Kozik cyclic terms supply WNUs of all large prime (hence odd) arities.

## Depends on

- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](bulatov-zhuk-csp-dichotomy-theorem.md)
- [Barto–Kozik: finite idempotent Taylor algebras have cyclic terms of every prime arity above the domain size](barto-kozik-cyclic-terms-prime-arity.md)

## Proof depends on

- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](bulatov-zhuk-csp-dichotomy-theorem.md)
- [Barto–Kozik: finite idempotent Taylor algebras have cyclic terms of every prime arity above the domain size](barto-kozik-cyclic-terms-prime-arity.md)
- [Maróti–McKenzie: finite Taylor algebras have weak near-unanimity terms](maroti-mckenzie-taylor-implies-wnu.md)

## Sources

- Dmitriy Zhuk, "A simplified proof of the CSP Dichotomy Conjecture and XY-symmetric operations", arXiv preprint (2024), arXiv:2404.01080.
