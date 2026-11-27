# Williams: improving exhaustive search for Circuit-SAT implies NEXP is not in P/poly

If there is a deterministic algorithm that decides satisfiability of Boolean circuits with $n$ inputs and size $\operatorname{poly}(n)$ in time $2^{n}/n^{\omega(1)}$ (for every polynomial size bound, with the superpolynomial saving uniform in the polynomial), then $\mathrm{NEXP} \not\subseteq \mathrm{P}/\mathrm{poly}$. The same conclusion follows from a non-trivial deterministic algorithm for the Circuit Acceptance Probability Problem.

## Proof sketch

Assume $\mathrm{NEXP} \subseteq \mathrm{P}/\mathrm{poly}$; by the easy witness lemma every $\mathrm{NEXP}$ verifier has polynomial-size circuit witnesses. Take a language in $\mathrm{NTIME}[2^n]$ not in $\mathrm{NTIME}[2^n/n^{\omega(1)}]$, reduce it to succinct $3$-SAT with a quasi-linear PCP, guess circuits for a satisfying assignment, and check the composition with the non-trivial SAT algorithm on the circuit that searches for a violated clause, contradicting the nondeterministic time hierarchy.

## Depends on

- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Non-trivial satisfiability and derandomization algorithms for a circuit class](nontrivial-circuit-analysis.md)

## Proof depends on

- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](easy-witness-ikw.md)
- [Short PCPs with projection queries for nondeterministic time](short-pcp-projection.md)

## Sources

- R. Williams, "Improving exhaustive search implies superpolynomial lower bounds", SIAM Journal on Computing 42 (2013) 1218-1244; STOC (2010).
