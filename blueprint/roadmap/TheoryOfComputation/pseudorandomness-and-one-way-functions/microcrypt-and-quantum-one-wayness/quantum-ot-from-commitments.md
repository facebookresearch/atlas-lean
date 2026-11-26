# Oblivious transfer and secure computation from quantum commitments

Assume quantum-secure one-way functions (or, more generally, any quantum bit commitments with suitable extractability and equivocality, which can be built from them). Then there is a maliciously simulation-secure oblivious transfer protocol with quantum communication (based on BB84 states, where the receiver commits to its measurement bases and outcomes and the sender checks a random subset), and hence, via the completeness of OT, maliciously secure computation of every classical functionality. Unlike classical cryptography, where OT requires public-key assumptions, this places OT in MiniQCrypt; later work showed the commitments may be replaced by any quantum commitments (hence EFI).

## Proof sketch

The receiver measures BB84 qubits sent by the sender, commits to bases and outcomes, and the sender opens random checks; extractable and equivocal commitments (built from OWF with quantum-secure techniques) give simulation of both parties. Privacy amplification via universal hashing removes the receiver's partial information about the unchosen string.

## Depends on

- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- James Bartusek, Andrea Coladangelo, Dakshita Khurana, Fermi Ma, "One-Way Functions Imply Secure Computation in a Quantum World", CRYPTO (2021), arXiv:2011.13486.
- Alex B. Grilo, Huijia Lin, Fang Song, Vinod Vaikuntanathan, "Oblivious Transfer is in MiniQCrypt", EUROCRYPT (2021), IACR ePrint 2020/1500.
