# Nondeterministic quasi-polynomial time

For $k \ge 1$ let $\mathrm{NTIME}[2^{\log^{k} n}]$ be the class of languages decided by nondeterministic multi-tape Turing machines running in time $2^{O(\log^{k} n)}$. **Nondeterministic quasi-polynomial time** is

$$
\mathrm{NQP} = \bigcup_{k \ge 1} \mathrm{NTIME}\bigl[2^{\log^{k} n}\bigr].
$$

It satisfies $\mathrm{NP} \subseteq \mathrm{NQP} \subseteq \mathrm{NEXP}$, and both inclusions are strict by the nondeterministic time hierarchy theorem.

## Depends on

- [Nondeterministic time hierarchy](../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)

## Sources

- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
