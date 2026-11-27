# Binary syndrome decoding gap hardness

For block length $n>0$, take a binary parity-check matrix $H$ with $n$ columns, a binary syndrome $s$ with one coordinate per row of $H$, and an integer radius $r>0$. In a yes instance there is $z\in\mathbb F_2^n$ with $Hz=s$ and $\operatorname{wt}(z)\le r$. In a no instance there is at least one $z$ with $Hz=s$, and every such $z$ has $\operatorname{wt}(z)>n^{1/200}r$. In particular an inconsistent syndrome is outside both promises. This promise problem is NP-hard under deterministic polynomial-time reductions.

## Depends on

- [Binary promise reductions for lattice and decoding problems](promise-reductions-for-lattices-and-linear-codes.md)

## Proof depends on

- [Binary nearest-codeword gap hardness](binary-nearest-codeword-gap-hardness.md)

## Expansion

Construct and verify the generator-to-parity-check transformation with the same block length, including reachable syndrome and exact correspondence of Hamming distances. The existing exact decoding problem treats inconsistent syndromes differently and has no approximation gap.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 7](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `binarySyndromeDecodingIsNPHard`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L268-L269)
