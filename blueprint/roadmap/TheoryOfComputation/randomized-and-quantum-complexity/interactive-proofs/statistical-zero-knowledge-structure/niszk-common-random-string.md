# Non-interactive statistical zero knowledge NISZK in the common random string model

A promise problem $\Pi$ is in $\mathsf{NISZK}$ if there are a computationally unbounded prover $P$, a deterministic polynomial-time verifier $V$, a polynomial $\ell$ and a probabilistic polynomial-time simulator $S$ such that, for a common random string $\sigma\sim\{0,1\}^{\ell(|x|)}$ and a single message $\pi=P(x,\sigma)$:

1. completeness: for $x\in\Pi_{\mathrm{yes}}$, $\Pr_\sigma[V(x,\sigma,P(x,\sigma))=1]\ge 1-\mathrm{negl}(|x|)$;
2. soundness: for $x\in\Pi_{\mathrm{no}}$, $\Pr_\sigma[\exists\pi:V(x,\sigma,\pi)=1]\le\mathrm{negl}(|x|)$;
3. zero knowledge: for $x\in\Pi_{\mathrm{yes}}$, $S(x)$ is statistically close to $(\sigma,P(x,\sigma))$.

Every $\mathsf{NISZK}$ proof is an honest-verifier $\mathsf{SZK}$ proof (the verifier sends $\sigma$), so $\mathsf{NISZK}\subseteq\mathsf{HVSZK}=\mathsf{SZK}$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [Zero-knowledge interactive proofs](../../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013.
