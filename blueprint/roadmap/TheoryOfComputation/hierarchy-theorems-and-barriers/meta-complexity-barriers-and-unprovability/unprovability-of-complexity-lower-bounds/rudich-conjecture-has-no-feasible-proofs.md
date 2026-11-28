# Rudich's conjecture does not admit feasible propositional proofs

Pich and Santhanam prove unconditionally that no propositional proof system can efficiently prove, for most truth tables, that a fixed non-uniform proof system lacks short proofs of the corresponding circuit lower bound. If Rudich's conjecture is true, its truth implies its own feasible unprovability.

Rudich's conjecture states that there is $c > 0$ such that every language $L \subseteq \overline{\mathrm{MCSP}[n^c]}$ in $\mathsf{NSIZE}(\mathrm{poly})$ is $1/N^{\omega(1)}$-sparse, where $N$ is the input length. The conjecture admits feasible propositional proofs if for every large enough integer $d$ and every propositional proof system $R$ with polynomial advice there is a propositional proof system $S$ such that, for every sequence $\{w_m\}$ of polynomial-size advice strings good for $R$, for all large enough $n$ and a $1 - o(1)$ fraction of $f_n \colon \{0,1\}^n \to \{0,1\}$, the formula $\mathrm{lb}_R(\mathrm{tt}(f_n, n^d), m^d, w_m)$ has polynomial-size $S$-proofs, where $m = |\mathrm{tt}(f_n, n^d)|$.

**Theorem.** Rudich's conjecture does not admit feasible propositional proofs.

Moreover, if Rudich's conjecture holds, there are a propositional proof system $R$ and a samplable sequence of distributions $\{D_N\}$ on formulas of length $\mathrm{poly}(N)$ such that with probability $1 - 1/N^{\omega(1)}$ a sample $\varphi_N$ is a tautology without $\mathrm{poly}(N)$-size $R$-proofs, yet for some constant $k$ no propositional proof system has polynomial-size proofs of $\mathrm{lb}_R(\varphi_N, |\varphi_N|^k)$.

## Proof sketch

If the conjecture fails, a proof system with advice proves most circuit lower-bound tautologies quickly for infinitely many $n$, so the formulas $\mathrm{lb}_R(\cdot)$ are mostly false and no sound $S$ proves them. If the conjecture holds, it is used three times: to make most $\mathrm{tt}(f_n, n^d)$ hard for $R$, to show that the truth table of MCSP itself is hard, so that the corresponding tautologies can be added as axioms of a proof system $R$, and to build a set of hitting tautologies that are easy for $R$. Soundness of $S$ forbids short $S$-proofs of $\mathrm{lb}_R$ for the easy hitting tautologies, and short proofs for random ones would then contradict the hitting property. The result is a proof-complexity analogue of the natural proofs barrier.

## Depends on

- [Rudich's conjecture](rudich-s-conjecture.md)
- [Circuit lower-bound tautologies and proof-size lower-bound formulas](circuit-lower-bound-tautologies.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

None.

## Sources

- Ján Pich and Rahul Santhanam, "Why are Proof Complexity Lower Bounds Hard?", *FOCS* 2019, DOI 10.1109/FOCS.2019.00080 (Theorem 1 and Corollary 1, Section 1.3; Rudich's conjecture and Definition 7, Section 2.3; proof as Theorem 5 and Corollary 2, in the authors' full version of 5 April 2019, <https://ora.ox.ac.uk/objects/uuid:b038d171-928d-4dfe-abf5-a6fdb03217b2>).
