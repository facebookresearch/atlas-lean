# Lose-lose theorem for extended Frege and circuit lower bounds

Under Rudich's conjecture and a hardness assumption for E, either extended Frege cannot efficiently prove any superpolynomial circuit lower bound, or there are explicit sets of tautologies, mostly hard for extended Frege, whose hardness no proof system can efficiently establish.

Assume Rudich's conjecture and that there is $\epsilon > 0$ with $\mathsf{E} \not\subseteq \mathsf{io}\text{-}\mathsf{NSIZE}(2^{\epsilon n})$. Then at least one of the following holds:

1. there is no sequence of Boolean functions $f_n$ on $n$ bits such that $\mathrm{tt}(f_n, n^k)$ has polynomial-size $\mathsf{EF}$-proofs for every $k > 0$;
2. for each $k > 0$ and each propositional proof system $Q$ there is a polynomial-time algorithm that on input $1^N$, $N = 2^n$, outputs a set $S_N$ of truth tables of functions on $n$ bits such that for each large enough $N$ some $F \in S_N$ makes $\mathrm{tt}(\mathrm{fn}(F), n^k)$ a tautology with no $\mathsf{EF}$-proofs of size $N^k$, while $\mathrm{lb}_{\mathsf{EF}}(\mathrm{tt}(\mathrm{fn}(F), n^k), N^k)$ has no $Q$-proofs of size $N^{k^2}$.

Informally: either $\mathsf{EF}$ efficiently proves no superpolynomial circuit lower bound, or there are explicit polynomial-time generable sets of formulas, mostly tautologies hard for $\mathsf{EF}$, whose hardness for $\mathsf{EF}$ no proof system can efficiently establish. The same argument gives the analogous statement for Frege.

## Expansion

Thus, under these hardness assumptions, either the circuit lower bounds program cannot be carried out inside $\mathsf{EF}$, or the Cook–Reckhow program of proving superpolynomial lower bounds for $\mathsf{EF}$ meets an inherent obstacle. The proof combines the hitting-tautology argument behind the unprovability of Rudich's conjecture with a derandomization step: a complexity-theoretic pseudorandom generator against nondeterministic circuits, available when $\mathsf{E}$ requires exponential-size nondeterministic circuits, turns the random tautologies into explicit polynomial-time generable sets $S_N$.

## Depends on

- [Circuit lower-bound tautologies and proof-size lower-bound formulas](circuit-lower-bound-tautologies.md)
- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Rudich's conjecture does not admit feasible propositional proofs](rudich-conjecture-has-no-feasible-proofs.md)

## Sources

- Ján Pich and Rahul Santhanam, "Why are Proof Complexity Lower Bounds Hard?", *FOCS* 2019, DOI 10.1109/FOCS.2019.00080 (Theorem 3, Section 1.3, its rigorous form Theorem 8, and Theorem 4 on generators against nondeterministic circuits, Section 2.4, in the full version read).
