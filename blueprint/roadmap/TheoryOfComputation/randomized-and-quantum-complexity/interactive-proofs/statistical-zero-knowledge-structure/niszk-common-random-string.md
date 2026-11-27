# Non-interactive statistical zero knowledge NISZK in the common random string model

A promise problem $\Pi$ is in $\mathsf{NISZK}$ if there are a computationally unbounded probabilistic prover $P$, a probabilistic polynomial-time verifier $V$, a probabilistic polynomial-time simulator $S$ and a polynomial $\ell$ such that, for a common random string $\sigma$ uniform on $\{0,1\}^{\ell(|x|)}$ and a single message $\pi=P(x,\sigma)$ from the prover to the verifier:

1. completeness: for $x\in\Pi_{\mathrm{yes}}$, $V(x,\sigma,P(x,\sigma))$ accepts with probability at least $2/3$;
2. soundness: for $x\in\Pi_{\mathrm{no}}$ and every prover strategy $P^*$, $V(x,\sigma,P^*(x,\sigma))$ accepts with probability at most $1/3$;
3. zero knowledge: for $x\in\Pi_{\mathrm{yes}}$, the statistical distance between $S(x)$ and $(\sigma,P(x,\sigma))$ is at most $\beta(|x|)$ for a negligible function $\beta$.

The probabilities in 1 and 2 are over $\sigma$ and the coins of the verifier and the prover. Non-interactive statistical zero knowledge is closed under parallel repetition (with independent common random strings), so the completeness and soundness errors can be made exponentially small in $|x|$.

Every $\mathsf{NISZK}$ proof is an honest-verifier $\mathsf{SZK}$ proof (the verifier sends $\sigma$), so $\mathsf{NISZK}\subseteq\mathsf{HVSZK}=\mathsf{SZK}$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [Zero-knowledge interactive proofs](../../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013.
