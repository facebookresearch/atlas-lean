# Paturi–Pudlák–Zane: depth-three circuits for parity

For every $k \ge 1$, every $\Sigma_3^k$ formula computing the parity of $n\ge 1$ variables has size at least $2^{n/k-1}$; that is, $\Sigma_3^k(\oplus_n) \ge 2^{n/k-1}$ (for $k=n$ a single CNF suffices, so the factor $1/2$ cannot be dropped in general). With unrestricted bottom fan-in, every depth-three OR-of-ANDs-of-ORs circuit computing $\oplus_n$ has $\Omega(n^{1/4} 2^{\sqrt{n}})$ gates, and the same bound holds for $\Pi_3$ circuits.

## Proof sketch

Each CNF in the disjunction has all its solutions among the true inputs of parity, which are isolated; so each true input is an isolated solution of one of the CNFs. By the satisfiability coding lemma a width-$k$ CNF has at most $2^{(1-1/k)n}$ isolated solutions, so at least $2^{n-1}/2^{(1-1/k)n} = 2^{n/k - 1}$ formulas are needed. For unrestricted bottom fan-in, PPZ weight the isolated solutions by the lengths of their critical clauses and balance the number of CNFs against the number of clauses.

## Depends on

- [Depth-three $\Sigma_3^k$ formulas](depth-three-sigma3-formulas.md)
- [Isolated true inputs of a Boolean function](isolated-true-inputs.md)

## Proof depends on

- [A $k$-CNF has at most $2^{(1-1/k)n}$ isolated solutions](../../../../fine-grained-complexity/exponential-sat-algorithms/k-cnf-isolated-solutions-bound.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999, Article 11 (Lemma 4 and Theorem 6).
