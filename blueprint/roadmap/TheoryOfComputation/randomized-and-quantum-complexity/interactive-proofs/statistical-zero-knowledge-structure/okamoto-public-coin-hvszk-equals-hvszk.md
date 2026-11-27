# Okamoto: public-coin HVSZK equals HVSZK

Every promise problem with an honest-verifier statistical zero-knowledge proof has one in which the verifier is public-coin, that is, sends only uniformly random strings and decides by a deterministic predicate of the transcript: public-coin $\mathsf{HVSZK}=\mathsf{HVSZK}$. This is the zero-knowledge analogue of the Goldwasser–Sipser transformation from private to public coins, but with zero knowledge preserved.

## Proof sketch

Okamoto's original proof was intricate. Goldreich and Vadhan gave a short proof: reduce the problem to $\mathrm{ED}$ by the Karp reduction, then run the public-coin $\mathsf{HVSZK}$ protocol for $\mathrm{ED}$ on the reduced instance; Karp reductions preserve both proof completeness and statistical zero knowledge.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)

## Proof depends on

- [Goldwasser-Sipser: private coins add no power to interactive proofs](../../goldwasser-sipser-theorem/goldwasser-sipser.md)
- [Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference](every-hvszk-problem-reduces-to-ed.md)
- [Goldreich–Vadhan: Entropy Difference has a public-coin honest-verifier statistical zero-knowledge proof](entropy-difference-has-public-coin-hvszk-proof.md)

## Sources

- Tatsuaki Okamoto, "On Relationships between Statistical Zero-Knowledge Proofs", Journal of Computer and System Sciences 60(1) (2000).
- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
