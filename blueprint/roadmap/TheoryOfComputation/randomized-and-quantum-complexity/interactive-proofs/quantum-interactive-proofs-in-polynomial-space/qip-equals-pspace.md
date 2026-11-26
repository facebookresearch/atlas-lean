# QIP = PSPACE

$\mathrm{QIP} = \mathrm{PSPACE} = \mathrm{IP}$. Consequently quantum interaction gives no additional power beyond classical interaction for single-prover interactive proofs, while three messages suffice for all of $\mathrm{PSPACE}$ with quantum communication.

## Proof sketch

$\mathrm{PSPACE} = \mathrm{IP} \subseteq \mathrm{QIP}$ by Shamir's theorem and the simulation of classical by quantum verifiers, and $\mathrm{QIP} \subseteq \mathrm{PSPACE}$ by the multiplicative weights algorithm. The three-message statement is the Kitaev-Watrous parallelization.

## Depends on

- [Quantum interactive proofs (QIP) and IP subset QIP](../../quantum-interactive-proofs-and-ip-subset-qip.md)

## Proof depends on

- [QIP is contained in PSPACE (Jain-Ji-Upadhyay-Watrous)](qip-is-contained-in-pspace.md)
- [IP = PSPACE (Shamir)](../../ip-eq-pspace.md)
- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)

## Sources

- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
