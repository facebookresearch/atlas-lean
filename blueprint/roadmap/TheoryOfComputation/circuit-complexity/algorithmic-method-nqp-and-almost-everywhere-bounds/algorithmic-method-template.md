# The algorithmic method template: non-trivial algorithms imply lower bounds

Let $\mathcal{C}$ be a typical circuit class (evaluatable in deterministic polynomial time and closed under negation and conjunctions, as in Murray–Williams §1.1), and let $\varepsilon \in (0, 1)$. If $\mathrm{GapCUnsat}$ on $n$-input, $2^{n^{\varepsilon}}$-size $\mathcal{C}$-circuits is solvable in nondeterministic time $O(2^{n - n^{\varepsilon}})$, then for every $k \ge 1$ there is $c \ge 1$ such that $\mathrm{NTIME}[2^{\log^{c k^4/\varepsilon} n}]$ does not have $2^{\log^k n}$-size $\mathcal{C}$-circuits; in particular,

$$
\mathrm{NQP} \not\subseteq \mathcal{C}\text{-}\mathrm{SIZE}[2^{\operatorname{polylog}(n)}].
$$

With a non-trivial ($2^n / n^{\omega(1)}$-time) satisfiability or derandomization algorithm only for polynomial-size $\mathcal{C}$-circuits (or $\mathrm{AND}_3 \circ \mathcal{C}$ / suitable composition), Williams's theorem yields $\mathrm{NEXP} \not\subseteq \mathcal{C}\text{-}\mathrm{SIZE}[\operatorname{poly}(n)]$.

## Proof sketch

Suppose $\mathrm{NQP} \subseteq \mathcal{C}\text{-}\mathrm{SIZE}[2^{\log^k n}]$. By the easy witness lemma for $\mathrm{NQP}$ (together with circuit evaluation lying in $\mathrm{P} \subseteq \mathrm{NQP}$), every $\mathrm{NQP}$ verifier has quasi-polynomial-size $\mathcal{C}$-circuit witnesses. Given a language in $\mathrm{NTIME}[2^{\log^{c k^4/\varepsilon} n}]$ hard for smaller nondeterministic time by the nondeterministic time hierarchy, reduce it to succinct $3$-SAT via short PCPs with projection queries, guess quasi-polynomial-size $\mathcal{C}$-circuits for a witness and for the PCP proof, and apply the $O(2^{n - n^{\varepsilon}})$-time $\mathrm{GapCUnsat}$ algorithm to the composed circuit; the exponential saving absorbs the guessed witness-circuit description and contradicts the nondeterministic time hierarchy.

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
