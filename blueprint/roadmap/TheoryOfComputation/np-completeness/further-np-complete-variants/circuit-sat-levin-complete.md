# Circuit satisfiability is complete for PC under Levin reductions

A **Levin reduction** from a relation $R$ to $R'$ is a pair of polynomial-time maps $(f,g)$ such that $f$ is a Karp reduction of $S_R=\{x:\exists y\,(x,y)\in R\}$ to $S_{R'}$ and, for every $x\in S_R$ and every $y'$ with $(f(x),y')\in R'$, $(x,g(x,y'))\in R$. The circuit-satisfaction relation $R_{\mathrm{CSAT}}=\{(C,z):C(z)=1\}$ is $\mathsf{PC}$-complete under Levin reductions, and so is SAT's witness relation, via the Cook–Levin reduction. The reductions constructed in the proofs also map witnesses of $R$ to witnesses of $R'$ in polynomial time.

## Proof sketch

For a $\mathsf{PC}$ relation with polynomial-time decider $V$ and witness length bound $p$, map $x$ to a circuit that, on a suitably encoded candidate $y$ of length at most $p(|x|)$, computes $V(x,y)$; the backward map decodes the circuit input, witnesses map forward by encoding, and for SAT the tableau variables of the Cook–Levin formula determine the circuit input.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](../../complexity-classes/structural-complexity/search-problems-and-self-reducibility/self-reducible-search-problems.md)
- [CIRCUIT SAT is NP-complete](../satisfiability/circuit-satisfiability/circuit-sat-np-complete.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Definition 2.12, Theorems 2.21 and 2.22.
- Leonid A. Levin, "Universal Sequential Search Problems", Problems of Information Transmission 9(3), 265–266, 1973.
