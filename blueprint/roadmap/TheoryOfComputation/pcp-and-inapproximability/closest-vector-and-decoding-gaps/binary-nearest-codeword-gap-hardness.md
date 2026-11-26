# Binary nearest-codeword gap hardness

For block length $n>0$, take a binary matrix $G$ with $n$ rows and $k$ columns, a binary target $a\in\mathbb F_2^n$, and an integer radius $r>0$. The coefficient dimension $k$ need not be the rank of $G$. In a yes instance some $z\in\mathbb F_2^k$ has $\operatorname{wt}(a-Gz)\le r$; in a no instance every $z$ has $\operatorname{wt}(a-Gz)>n^{1/200}r$, with comparison in the reals. This promise problem is NP-hard under deterministic polynomial-time reductions.

## Depends on

- [Binary promise reductions for lattice and decoding problems](promise-reductions-for-lattices-and-linear-codes.md)

## Expansion

Verify the binary generator representation, Hamming weight and bit-size invariants in the gap reduction. Prove promise separation at n=1 and larger lengths; a decision-only reduction cannot substitute for the strict distance soundness clause.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 7](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `binaryNearestCodewordIsNPHard`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L212-L213)
