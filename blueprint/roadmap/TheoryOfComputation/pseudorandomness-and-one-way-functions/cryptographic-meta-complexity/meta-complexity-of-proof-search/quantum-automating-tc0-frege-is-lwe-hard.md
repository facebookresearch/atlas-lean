# Arteche–Carenini–Gray: quantum algorithms cannot weakly automate TC0-Frege unless LWE is broken

If a polynomial-time quantum algorithm weakly automates $\mathrm{TC}^0_d$-Frege for a large enough constant depth $d$, then Learning with Errors is broken by uniform polynomial-size quantum circuits: the first hardness result for proof search by quantum algorithms.

A propositional proof system $S$ is **quantum automatable** (in time $t$) if a quantum Turing machine, on input a formula $\varphi$, outputs an $S$-proof of $\varphi$ whenever one exists, in expected time $t(\mathrm{size}_S(\varphi))$, with $t$ polynomial; equivalently, a uniform family of quantum circuits $C_{n,s}$ of size $(n+s)^{c}$ outputs, with probability at least $2/3$, an $S$-proof of size $s^{c}$ of any size-$n$ formula having a proof of size $s$. It is **weakly** quantum automatable if such an algorithm outputs proofs in some other proof system $Q$ in time $\mathrm{size}_S(\varphi)^{O(1)}$. The LWE assumption states that for $m=n^{O(1)}$, $q\le 2^{n^{O(1)}}$, a uniform secret $s\in\mathbb{Z}_q^{n}$, a uniform $A\in\mathbb{Z}_q^{m\times n}$ and discrete Gaussian error $\varepsilon$ of width $\alpha q$ with $\alpha=o(1)$, no quantum $n^{O(1)}$-time algorithm recovers $s$ from $(A,As+\varepsilon)$ with noticeable probability.

**Theorem.** There is a constant $d_0$ such that for every $d\ge d_0$: if a polynomial-time quantum algorithm weakly automates $\mathrm{TC}^0_d$-Frege, then LWE is broken by a P-uniform family of polynomial-size quantum circuits; if the weak automating algorithm is classical, LWE is broken by a uniform family of polynomial-size Boolean circuits. For $\mathrm{AC}^0_d$-Frege the same conclusion holds with circuits of size $2^{n^{o(1)}}$. The conclusions already follow if $\mathrm{TC}^0_d$-Frege (respectively $\mathrm{AC}^0_d$-Frege) has feasible interpolation by (quantum) circuits.

## Expansion

The quantum version of Impagliazzo's observation says that a quantum automatable proof system closed under restrictions has feasible interpolation by quantum circuits: run the automating algorithm on the restricted formula and check the proof; unlike the randomized case, the quantum interpolant cannot be derandomized by Adleman's trick. Then encode the injective LWE function $f_A(s,\varepsilon)=As+\varepsilon\bmod q$ as the split contradiction $(f_A(x)=z\wedge x_1=0)\wedge(f_A(y)=z\wedge y_1=1)$. Since $f_A$ is injective only for most $A$, the formula is instantiated with a concrete hardwired $A_0$ having a certificate of injectivity: a left inverse of $A_0$ together with $m$ linearly independent short vectors in the dual $q$-ary lattice, which certify via the left inequality of Banaszczyk's transference theorem that $\lambda_1(L_q(A_0))$ is large; such certificates exist with high probability by the right inequality. Injectivity from a certificate is proved in a theory $\mathrm{LA}_{\mathbb Q}$ of rational linear algebra whose theorems have succinct $\mathrm{TC}^0$-Frege proofs. A quantum interpolant then recovers the secret bit by bit, breaking LWE. The result extends the classical non-automatability theorems of Krajíček–Pudlák, Bonet–Pitassi–Raz and Bonet–Domingo–Gavaldà–Maciel–Pitassi, which rely on factoring-type assumptions that quantum algorithms break.

## Depends on

- [Automatable proof systems](../../../../Logic/proof-theory/automatability-of-proof-systems/automatable-proof-system.md)

## Proof depends on

- [Automatability implies feasible interpolation for systems closed under restriction](../../../../Logic/proof-theory/automatability-of-proof-systems/automatability-implies-interpolation.md)
- [Frege-type systems are not automatable under cryptographic assumptions](../../../../Logic/proof-theory/automatability-of-proof-systems/bpr-frege-non-automatable.md)

## Sources

- Noel Arteche, Gaia Carenini and Matthew Gray, "Quantum Automating TC0-Frege Is LWE-Hard", *Computational Complexity*, 2025, https://doi.org/10.1007/s00037-025-00271-w; numbering from arXiv:2402.10351v3 (Assumption 2.6, Definitions 3.1, 3.3, 3.5 and 3.7, Propositions 3.6, 3.8 and 3.10, Theorem 4.1, Corollaries 4.2 and 4.12, Definitions 4.3 and 4.5).
