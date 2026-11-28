# COMPONENT SUM AT MOST B WITH THREE PARTS AND 0/1 ENTRIES as a decision problem

The decision problem COMPONENT SUM AT MOST B WITH THREE PARTS AND 0/1 ENTRIES accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(m, C, K, B)$, to an instance that is [well-formed](../part-08/well-formed-2-4.md) and [feasible](../part-07/upper-bound-feasible.md) for COMPONENT SUM AT MOST B, the three parts and the 0/1 entries being part of [well-formedness](../part-08/well-formed-2-4.md). It rejects every bitstring that does not decode to such an instance.
