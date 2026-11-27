# Binary promise reductions for lattice and decoding problems

A promise problem is a pair of disjoint languages of finite bit strings, the yes instances and the no instances. A deterministic polynomial-time many-one reduction from a bit language sends members to yes instances and all nonmembers to no instances. Hardness here quantifies over all languages with polynomial-length binary certificates checked by a polynomial-time verifier. Strings outside a promise need not be decided.

The pinned representation encodes each atomic natural, integer or rational through its natural-number code, then its binary word $w$, prefixed by $|w|$ one bits and a zero. Vectors are concatenated in index order and matrices row by row. The lattice record lists dimension and radius, then target coordinates and basis entries. A generator-matrix code record lists block length, coefficient dimension and radius, then target and generator; a parity-check record lists check count, block length and radius, then syndrome and parity-check matrix. Binary field entries are encoded as integers zero and one.

## Expansion

Prove unique decoding and polynomial-time conversions to the standard binary encodings and verifier model. Establish disjointness for each promise from the inequalities and unique decoding before crediting any hardness result. Numeric field sizes and bit lengths are different resources.

## Sources

- [Pinned atomic and list encodings and certificate model](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L9-L57)
- [Pinned promise and reduction definitions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L130-L151)
- [Pinned lattice and code record encodings](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L63-L78)
- [Pinned nearest codeword encoding](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L156-L171)
- [Pinned syndrome encoding](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L216-L231)
