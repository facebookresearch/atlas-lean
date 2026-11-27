# Partial MCSP is in NP

Partial MCSP is in NP for unary and for binary encodings of the size threshold: a certificate is a circuit of size at most $s$, and the verifier checks agreement on the defined entries of the partial truth table.

## Proof sketch

As for MCSP, the circuit is evaluated on the at most $2^n$ defined inputs; the certificate length is polynomially bounded since thresholds beyond the Shannon bound are trivial.

## Depends on

- [Partial MCSP (MCSP*)](partial-minimum-circuit-size-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [The Shannon–Lupanov window for MCSP](shannon-lupanov-window-for-mcsp.md)

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
