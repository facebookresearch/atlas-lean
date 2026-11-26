# Multi-prover interactive proofs MIP

In a $k$-prover interactive proof, a probabilistic polynomial-time verifier exchanges messages with $k$ computationally unbounded provers that may agree on a strategy in advance but cannot communicate during the protocol (each prover's answers depend only on the messages it received). $\mathsf{MIP}_k$ is the class of languages with such proofs of completeness $\ge2/3$ and soundness $\le1/3$; $\mathsf{MIP}=\bigcup_k\mathsf{MIP}_k$. Deterministic provers suffice, and the prover answers may be taken history-consistent. By Babai–Fortnow–Lund, $\mathsf{MIP}=\mathsf{MIP}_2=\mathsf{NEXP}$.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)

## Sources

- László Babai, Lance Fortnow and Carsten Lund, "Non-Deterministic Exponential Time Has Two-Prover Interactive Protocols", Computational Complexity 1(1), 1991.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
