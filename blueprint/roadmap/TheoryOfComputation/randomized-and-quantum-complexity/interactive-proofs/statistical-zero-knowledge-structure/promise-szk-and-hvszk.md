# Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems

A promise problem $\Pi=(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ is in $\mathsf{HVSZK}$ if there is an interactive proof $(P,V)$ with a computationally unbounded prover and a probabilistic polynomial-time verifier with completeness error and soundness error at most $1/3$, and a probabilistic polynomial-time simulator $S$ such that for every $x\in\Pi_{\mathrm{yes}}$ the statistical (total variation) distance between $S(x)$ and the view of $V$ in the interaction with $P$ on $x$ is negligible in $|x|$. It is in $\mathsf{SZK}$ if for every probabilistic polynomial-time verifier strategy $V^*$ there is such a simulator for the view of $V^*$; it is in public-coin $\mathsf{HVSZK}$ if moreover the verifier's messages are its random coins. Nothing is required of the simulator on $\Pi_{\mathrm{no}}$, and closure properties are stated for promise classes with Karp reductions between promise problems. Recall that $\mathrm{SD}^{\alpha,\beta}$, statistical difference, takes two circuits $(C_0,C_1)$ sampling distributions from uniform inputs and asks whether their statistical distance is at least $\alpha$ or at most $\beta$; Sahai and Vadhan proved $\mathrm{SD}^{2/3,1/3}$ complete for $\mathsf{HVSZK}$ via their polarization lemma, which works for constants with $\alpha^2>\beta$.

## Depends on

- [Statistical honest-verifier zero knowledge](../../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-proofs/stat-hvzk.md)
- [Zero-knowledge interactive proofs](../../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Polynomial-time reduction between promise problems](../../local-hamiltonian-problem/promise-reduces.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2) (2003), ECCC TR00-084.
- Oded Goldreich, Amit Sahai and Salil Vadhan, "Honest-Verifier Statistical Zero-Knowledge Equals General Statistical Zero-Knowledge", STOC (1998).
