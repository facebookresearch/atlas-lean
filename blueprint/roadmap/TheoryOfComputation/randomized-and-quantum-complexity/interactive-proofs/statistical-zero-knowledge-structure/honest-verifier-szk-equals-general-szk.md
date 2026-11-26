# Goldreich–Sahai–Vadhan: honest-verifier SZK equals general SZK

$\mathsf{HVSZK}=\mathsf{SZK}$: every promise problem with a statistical zero-knowledge proof against the honest verifier has one that is statistically zero knowledge against every probabilistic polynomial-time verifier strategy. The transformation incurs a polynomial overhead in communication and rounds.

## Proof sketch

By Okamoto the protocol can be assumed public-coin. Each verifier coin toss is replaced by a random selection protocol, a two-party coin-generation procedure in which a cheating verifier cannot bias the outcome much, and in which the outcome can be simulated by sampling an honest-verifier transcript and steering the coins to it. Statistical zero knowledge against arbitrary verifiers follows because any verifier strategy can affect only the coins, whose distribution remains statistically close to uniform, and soundness is preserved because a cheating prover also cannot bias the coins.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [Okamoto: public-coin HVSZK equals HVSZK](okamoto-public-coin-hvszk-equals-hvszk.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Honest-Verifier Statistical Zero-Knowledge Equals General Statistical Zero-Knowledge", STOC (1998).
