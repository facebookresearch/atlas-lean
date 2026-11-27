# Paturi–Pudlák–Zane: depth-three circuits for parity

Every depth-three circuit of AND, OR and NOT gates computing the parity of $n$ variables has $\Omega(n^{1/4}2^{\sqrt n})$ gates. This holds both for $\Sigma_3$ circuits (an OR of CNFs) and for $\Pi_3$ circuits (an AND of DNFs).

## Proof sketch

Consider a $\Sigma_3$ circuit; since the complement of parity is a parity function, the $\Pi_3$ case follows. Each of the $2^{n-1}$ accepted inputs is accepted by some CNF of the circuit and is an isolated solution of that CNF. Weight an isolated solution $x$ by $w(x)=\sum_i 1/|C(x,i)|$, where $C(x,i)$ is a shortest critical clause for variable $i$ at $x$; by the satisfiability coding lemma a CNF has at most $2^{n-\mu}$ isolated solutions of weight at least $\mu$. Balancing the number of CNFs against the number of short clauses with $\mu=\sqrt n+(\log n)/4$ gives the bound.

Derived here for bounded bottom fan-in: every $\Sigma_3^k$ formula computing parity of $n\ge1$ variables has size at least $2^{n/k-1}$. Each true input of parity is an isolated solution of one of the $k$-CNFs, and a $k$-CNF has at most $2^{(1-1/k)n}$ isolated solutions, so at least $2^{n-1}/2^{(1-1/k)n}=2^{n/k-1}$ formulas are needed (for $k=n$ a single CNF suffices, so the factor $1/2$ cannot be dropped in general).

## Depends on

- [Depth-three $\Sigma_3^k$ formulas](depth-three-sigma3-formulas.md)

## Proof depends on

- [Isolated true inputs of a Boolean function](isolated-true-inputs.md)
- [A $k$-CNF has at most $2^{(1-1/k)n}$ isolated solutions](../../../../fine-grained-complexity/exponential-sat-algorithms/k-cnf-isolated-solutions-bound.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999, Article 11 (Lemma 4, Lemma 5 and Theorem 6).
