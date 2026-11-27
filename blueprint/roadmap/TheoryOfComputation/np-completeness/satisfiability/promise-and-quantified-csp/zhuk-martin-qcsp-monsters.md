# Zhuk–Martin: QCSP monsters refute the Chen Conjecture (P, NP, coNP, PSPACE on three elements; DP and Θ2P on larger domains)

Let $\Gamma$ be a finite constraint language on a **three-element** domain containing all constants. Then $\mathrm{QCSP}(\Gamma)$ is in $\mathsf{P}$, NP-complete, coNP-complete, or PSPACE-complete, and each of the four cases occurs. In particular there is a three-element language with constants whose polymorphism algebra has EGP while $\mathrm{QCSP}(\Gamma)$ is coNP-complete (and even EGP languages with $\mathrm{QCSP}(\Gamma)\in\mathsf{P}$), so the Chen Conjecture fails unless $\mathsf{coNP}=\mathsf{PSPACE}$. Moreover: there is a constraint language with constants on a **four-element** domain with $\mathrm{QCSP}(\Gamma)$ complete for $\mathsf{DP}$ (the second level of the Boolean hierarchy), and one on a **ten-element** domain with $\mathrm{QCSP}(\Gamma)$ complete for $\Theta_2^{\mathsf{P}}=\mathsf{P}^{\mathsf{NP}[O(\log n)]}$. Hence the complexity landscape of finite-domain QCSP with constants is strictly richer than a trichotomy (under standard assumptions).

## Proof sketch

For three elements, the algebraic analysis splits on whether the idempotent polymorphism algebra has PGP; in the EGP case Zhuk–Martin identify the precise obstacle: universally quantified variables can be restricted to a bounded number of "relevant" assignments except along one direction where the language behaves like a disjunction of coNP-type checks, giving coNP membership via a polynomial-size certificate for falsity. Hardness constructions encode UNSAT (for coNP) and combinations of SAT and UNSAT instances (for DP, and logarithmically many NP queries for $\Theta_2^{\mathsf{P}}$) into carefully designed relations on four and ten elements.

## Depends on

- [The Chen Conjecture on the complexity of QCSP](chen-conjecture-qcsp.md)
- [The class coNP](../../../complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)
- [Polynomially and exponentially generated powers (PGP and EGP)](polynomially-exponentially-generated-powers.md)
- [Quantified constraint satisfaction QCSP(Γ) over a finite constraint language](quantified-csp-over-finite-language.md)

## Proof depends on

- [Zhuk: every finite algebra has either polynomially or exponentially generated powers](zhuk-pgp-egp-dichotomy.md)
- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](../finite-domain-csp-dichotomy/bulatov-zhuk-csp-dichotomy-theorem.md)

## Sources

- Dmitriy Zhuk and Barnaby Martin, "QCSP Monsters and the Demise of the Chen Conjecture", STOC (2020); Journal of the ACM 69(5) (2022).
