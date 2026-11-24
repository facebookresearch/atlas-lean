# TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME as a decision problem

The decision problem TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(m, J, D)$ (a natural number, a list of lists of pairs of natural numbers and a natural number), to an instance that is well-formed for TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME and feasible for it (job completion times summing to at most the last component). It rejects every bitstring that does not decode to such an instance.
