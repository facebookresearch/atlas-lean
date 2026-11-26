# The algorithmic method template: non-trivial algorithms imply lower bounds

Let $\mathcal{C}$ be a circuit class closed under $\mathrm{AND}$, $\mathrm{OR}$ and projections. If there is a non-trivial derandomization algorithm for $\mathcal{C}$ circuits of size $2^{n^{\varepsilon}}$ for every $\varepsilon > 0$ (equivalently for the composition $\mathrm{AND}_{O(1)} \circ \mathcal{C}$), then

$$
\mathrm{NQP} \not\subseteq \mathcal{C}.
$$

With non-trivial algorithms only for polynomial-size circuits the conclusion is $\mathrm{NEXP} \not\subseteq \mathcal{C}$.

## Proof sketch

Suppose $\mathrm{NQP} \subseteq \mathcal{C}$. By the easy witness lemma for $\mathrm{NQP}$, every $\mathrm{NQP}$ verifier has $\mathcal{C}$-circuit witnesses. Given a language in $\mathrm{NTIME}[2^{\log^{k} n}]$ hard for smaller nondeterministic time by the hierarchy theorem, reduce it to succinct $3$-SAT via short PCPs with projection queries, guess $\mathcal{C}$-circuits for a witness and for the PCP proof, and use the non-trivial derandomization to check the PCP verifier composed with these circuits, achieving a nondeterministic speed-up that contradicts the nondeterministic time hierarchy.

## Depends on

- [Non-trivial satisfiability and derandomization algorithms for a circuit class](nontrivial-circuit-analysis.md)
- [Nondeterministic quasi-polynomial time](nqp-class.md)

## Proof depends on

- [Murray–Williams easy witness lemma for NQP and NP](mw-easy-witness-nqp.md)
- [Nondeterministic time hierarchy](../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)

## Sources

- R. Williams, "Improving exhaustive search implies superpolynomial lower bounds", SIAM Journal on Computing 42 (2013) 1218-1244; STOC (2010).
- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
- E. Ben-Sasson, E. Viola, "Short PCPs with projection queries", ICALP (2014).
