# Kitaev-Watrous: quantum interactive proofs parallelize to three messages

$\mathrm{QIP} = \mathrm{QIP}(3)$. More precisely, every problem in $\mathrm{QIP}$ has a three-message quantum interactive proof with perfect completeness and soundness error $2^{-p(n)}$ for any polynomial $p$.

## Proof sketch

First achieve perfect completeness by a standard modification. A three-message protocol then asks the prover for the verifier's private workspace at a uniformly chosen intermediate round, runs the protocol forward or backward one step, and checks consistency; a cheating prover must be inconsistent at some round, detected with probability inverse polynomial. Parallel repetition is sound for quantum interactive proofs with perfect completeness, driving soundness error down exponentially.

## Depends on

- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)

## Sources

- Alexei Kitaev, John Watrous, "Parallelization, amplification, and exponential time simulation of quantum interactive proof systems", STOC (2000).
