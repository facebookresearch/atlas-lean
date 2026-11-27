# Closest-vector gap hardness for finite rational p-norms

Fix a rational $p\ge1$. An input has dimension $n>0$, nonsingular integer basis matrix $B$, rational target $a\in\mathbb Q^n$, and positive rational radius $r$. With $\|x\|_p=(\sum_i|x_i|^p)^{1/p}$ evaluated over the reals, the yes promise is $\|Bz-a\|_p\le r$ for some $z\in\mathbb Z^n$, and the no promise is $\|Bz-a\|_p>n^{1/(200p)}r$ for every $z\in\mathbb Z^n$. There is no integrality requirement on the target in this version. The promise problem for each such $p$ is NP-hard under deterministic polynomial-time reductions.

## Depends on

- [Binary promise reductions for lattice and decoding problems](promise-reductions-for-lattices-and-linear-codes.md)

## Proof depends on

- [Binary nearest-codeword gap hardness](binary-nearest-codeword-gap-hardness.md)

## Expansion

Verify the p-norm lattice embedding and the exponent conversion from the binary gap. The statement fixes p before the problem, does not include p=∞, and requires full-rank square integral basis plus positive radius. Prove encoding and promise separation independently.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 7](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `finitePNormGapCVPIsNPHard`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L307-L308)
