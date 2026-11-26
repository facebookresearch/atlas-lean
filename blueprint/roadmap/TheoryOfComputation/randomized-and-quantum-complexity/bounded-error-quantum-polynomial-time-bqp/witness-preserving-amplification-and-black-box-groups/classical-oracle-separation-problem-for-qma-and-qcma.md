# The classical oracle separation problem for QMA and QCMA

The *QMA versus QCMA problem* asks whether quantum witnesses are more powerful than classical witnesses for efficient quantum verification. Relativized versions ask for an oracle $\mathcal{O}$ with $\mathrm{QMA}^{\mathcal{O}} \ne \mathrm{QCMA}^{\mathcal{O}}$: Aaronson and Kuperberg give such a separation relative to a quantum unitary oracle, and the *classical oracle separation problem* asks for a separating oracle $\mathcal{O}$ that is a Boolean function, accessed in superposition. Group Non-Membership, which Watrous placed in $\mathrm{QMA}$, is in $\mathrm{QCMA}$ by the Le Gall-Nishimura-Thakkar theorem, as Aaronson and Kuperberg conjectured, so it yields no such separation.

## Depends on

- [The class QCMA of quantum verification with classical witnesses](quantum-classical-merlin-arthur.md)
- [Aaronson-Kuperberg: a quantum oracle separates QMA from QCMA](quantum-oracle-separating-qma-from-qcma.md)
- [Le Gall-Nishimura-Thakkar: Order Verification is in QCMA](order-verification-is-in-qcma.md)

## Sources

- Scott Aaronson, Greg Kuperberg, "Quantum versus classical proofs and advice", Theory of Computing 3 (2007), CCC (2007); arXiv:quant-ph/0604056.
- Francois Le Gall, Harumichi Nishimura, Dhara Thakkar, "Group order is in QCMA", FOCS (2025); arXiv:2504.05547.
- John Watrous, "Succinct quantum proofs for properties of finite groups", FOCS (2000); arXiv:cs/0009002.
