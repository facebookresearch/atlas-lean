# Circuit satisfiability is complete for PC under Levin reductions

A **Levin reduction** from a relation $R$ to $R'$ is a triple of polynomial-time maps $(f,g,h)$ with $x\in S_R\iff f(x)\in S_{R'}$, $(x,y)\in R\Rightarrow(f(x),g(x,y))\in R'$, and $(f(x),y')\in R'\Rightarrow(x,h(x,y'))\in R$. The circuit-satisfaction relation (circuits paired with satisfying inputs) is $\mathsf{PC}$-complete under Levin reductions; the Cook–Levin reduction to SAT is also a Levin reduction, so SAT's witness relation is $\mathsf{PC}$-complete.

## Proof sketch

For a PC relation with polynomial-time decider $V$, map $x$ to the circuit computing $y\mapsto V(x,y)$ on inputs of the appropriate length; witnesses map to themselves, and the tableau variables of the Cook–Levin formula determine the certificate.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](../../complexity-classes/search-problems-and-self-reducibility/self-reducible-search-problems.md)
- [CIRCUIT SAT is NP-complete](../satisfiability/circuit-satisfiability/circuit-sat-np-complete.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 2.21.
- Leonid A. Levin, "Universal Sequential Search Problems", Problems of Information Transmission 9(3), 1973.
