# Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions

Let $(\mathbb{A}_1,\mathbb{B}_1)$ and $(\mathbb{A}_2,\mathbb{B}_2)$ be promise templates with finite signatures. If there is a minion homomorphism $\mathrm{Pol}(\mathbb{A}_1,\mathbb{B}_1)\to\mathrm{Pol}(\mathbb{A}_2,\mathbb{B}_2)$, then $\mathrm{PCSP}(\mathbb{A}_2,\mathbb{B}_2)$ reduces to $\mathrm{PCSP}(\mathbb{A}_1,\mathbb{B}_1)$ in logarithmic space (for both the decision and the search versions). Hence the complexity of $\mathrm{PCSP}(\mathbb{A},\mathbb{B})$ depends, up to log-space reductions, only on $\mathrm{Pol}(\mathbb{A},\mathbb{B})$ up to homomorphic equivalence of minions. Equivalently, every PCSP with a fixed template is log-space equivalent to the **promise minor condition** problem $\mathrm{PMC}_{\mathscr{M}}$ for $\mathscr{M}=\mathrm{Pol}(\mathbb{A},\mathbb{B})$: given a finite system $\Sigma$ of height-1 identities, distinguish "$\Sigma$ is trivial (satisfied by projections)" from "$\Sigma$ is not satisfiable in $\mathscr{M}$", an algebraic form of Gap Label Cover.

## Proof sketch

The reduction from $\mathrm{PCSP}(\mathbb{A}_2,\mathbb{B}_2)$ to the minor condition problem writes, for an instance $\mathbb{X}$, one function symbol per variable and constraint and height-1 identities encoding incidence; $\mathbb{X}\to\mathbb{A}_2$ makes the system trivial, while a solution in $\mathrm{Pol}(\mathbb{A}_2,\mathbb{B}_2)$ yields $\mathbb{X}\to\mathbb{B}_2$. Conversely a minor condition is turned into a PCSP instance over $\mathbb{A}_1$ using the free structure of the minion. Minion homomorphisms transport solutions of minor conditions, giving the composite reduction.

## Depends on

- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [Log-space many-one reductions](../../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)
- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)
- [Minions, minion homomorphisms and pp-constructions](../finite-domain-csp-dichotomy/minions-minion-homomorphisms-pp-constructions.md)

## Proof depends on

- [Barto–Opršal–Pinsker: pp-constructibility is captured by minion homomorphisms of polymorphisms](../finite-domain-csp-dichotomy/barto-oprsal-pinsker-pp-constructions-minion-homomorphisms.md)

## Sources

- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
