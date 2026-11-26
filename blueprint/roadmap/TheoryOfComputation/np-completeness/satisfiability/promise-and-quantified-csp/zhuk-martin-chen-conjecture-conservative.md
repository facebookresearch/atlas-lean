# Zhuk–Martin: the Chen Conjecture holds for finite conservative constraint languages

Let $\Gamma$ be a finite constraint language on a finite set $D$ that contains **all unary relations** on $D$ (a conservative language; every polymorphism then preserves every subset). If $(D;\mathrm{Pol}(\Gamma))$ has PGP, then $\mathrm{QCSP}(\Gamma)\in\mathsf{NP}$, and consequently (by the CSP dichotomy applied to the associated CSP) it is in $\mathsf{P}$ or NP-complete. Otherwise $\mathrm{Pol}(\Gamma)$ has EGP and $\mathrm{QCSP}(\Gamma)$ is PSPACE-complete.

## Proof sketch

For conservative algebras EGP manifests on a two-element subset $\{a,b\}$ on which all polymorphisms act as projections onto a subset of coordinates in a way that pp-defines a PSPACE-hard quantified Boolean problem, using the unary relations to restrict universally quantified variables to $\{a,b\}$. With PGP, one replaces each universal block by polynomially many tuples generating the corresponding power, reducing $\mathrm{QCSP}(\Gamma)$ to a polynomial-size $\mathrm{CSP}(\Gamma)$ instance.

## Depends on

- [The Chen Conjecture on the complexity of QCSP](chen-conjecture-qcsp.md)
- [Polynomially and exponentially generated powers (PGP and EGP)](polynomially-exponentially-generated-powers.md)
- [Quantified constraint satisfaction QCSP(Γ) over a finite constraint language](quantified-csp-over-finite-language.md)

## Proof depends on

- [Zhuk: every finite algebra has either polynomially or exponentially generated powers](zhuk-pgp-egp-dichotomy.md)
- [TQBF is PSPACE-complete](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)
- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](../finite-domain-csp-dichotomy/bulatov-zhuk-csp-dichotomy-theorem.md)

## Sources

- Dmitriy Zhuk and Barnaby Martin, "QCSP Monsters and the Demise of the Chen Conjecture", STOC (2020); Journal of the ACM 69(5) (2022).
