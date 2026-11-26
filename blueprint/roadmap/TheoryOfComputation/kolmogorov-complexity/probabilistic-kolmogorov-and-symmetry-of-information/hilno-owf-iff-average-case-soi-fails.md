# Hirahara–Ilango–Lu–Nanashima–Oliveira: one-way functions exist iff probabilistic time-bounded SoI fails on average

The following are equivalent:

1. Infinitely-often one-way functions do not exist.
2. Average-case symmetry of information for $\mathrm{pK}$ holds for every polynomial-time samplable family of pairs $\{D_n\}$ (with the same time bound $t(n)\ge p(n)$ on both sides and additive loss $\log t(n)$).
3. Average-case conditional coding holds for every such family.
4. Average-case language compression holds for every such family and every recursively enumerable $L$.

Moreover the high-probability ($1-1/q(n)$) and non-negligible-probability versions of items 2 to 4 are all equivalent, and the equivalence also holds with infinitely-often versions of items 2 to 4 against almost-everywhere one-way functions. Equivalently: one-way functions exist if and only if there is a samplable distribution of pairs $(x,y)$ on which time-bounded SoI for $\mathrm{pK}$ fails with non-negligible probability. This answers on average the question of Longpré and Mocas whether time-bounded SoI characterizes the non-existence of one-way functions.

## Proof sketch

Item 1 implies item 3 by the inversion-to-coding lemma, item 3 implies items 2 and 4 by the coding-to-SoI lemma, and item 4 implies item 1 by inverting through the universal sampler. Item 2 implies item 3: given SoI, apply it to the pair $(x,(y,r))$ built from the sampler so that the unconditional coding theorem for $\mathrm{pK}^t$ bounds the joint and marginal complexities, which leaves exactly the conditional coding bound.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [One-way functions exist](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Longpré–Mocas and Longpré–Watanabe: polynomial-time symmetry of information rules out one-way functions](longpre-watanabe-soi-implies-no-owf.md)
- [Inverting one-way functions yields average-case conditional coding for pK](inverting-owf-gives-average-case-conditional-coding.md)
- [Average-case conditional coding implies average-case symmetry of information and language compression](conditional-coding-implies-soi-and-compression.md)
- [Average-case language compression inverts every polynomial-time function via the universal sampler](language-compression-inverts-functions.md)
- [Lu–Oliveira–Zimand: an optimal coding theorem for pK^t over polynomial-time samplable distributions](optimal-coding-theorem-for-pkt.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
