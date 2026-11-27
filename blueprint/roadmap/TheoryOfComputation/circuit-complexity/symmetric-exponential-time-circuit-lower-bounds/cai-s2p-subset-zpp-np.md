# Cai: S2P is contained in ZPP^NP

$\mathrm{S}_2\mathrm{P}\subseteq\mathrm{ZPP}^{\mathrm{NP}}$: every language in $\mathrm{S}_2\mathrm{P}$ is decided by a zero-error probabilistic polynomial-time algorithm with an $\mathrm{NP}$ oracle. Relativizing and scaling up, $\mathrm{S}_2\mathrm{E}\subseteq\mathrm{ZPE}^{\mathrm{NP}}\subseteq\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E}$.

## Proof sketch

The algorithm maintains a small set of candidate proofs for one side and repeatedly samples a uniformly random proof for the other side; universal hashing and approximate counting with the $\mathrm{NP}$ oracle find a proof that defeats a constant fraction of the remaining opponents. After polynomially many rounds a short list of proofs certifies the answer, and the $\mathrm{NP}$ oracle verifies the certificate, so the algorithm never errs and only its running time is random.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](symmetric-alternation-s2p-s2e.md)
- [ZPP](../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Sources

- Jin-Yi Cai, "S_2^p is contained in ZPP^NP", Journal of Computer and System Sciences 73 (2007), ECCC TR01-030.
