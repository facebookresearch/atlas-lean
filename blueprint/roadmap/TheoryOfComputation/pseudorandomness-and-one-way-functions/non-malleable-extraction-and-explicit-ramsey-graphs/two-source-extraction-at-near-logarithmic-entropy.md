# Ben-Aroya-Doron-Ta-Shma: an efficient reduction from two-source to non-malleable extractors

There is an efficient reduction showing that a $t$-non-malleable extractor with seed length $d$ for min-entropy $k$ yields a two-source extractor whose min-entropy requirement is linear in $k + d$ up to factors polynomial (rather than exponential) in $t$; instantiated with known non-malleable extractors it gives explicit two-source extractors for min-entropy $O(\log n \cdot (\log\log n)^{O(1)})$, i.e. near-logarithmic, with constant error.

## Proof sketch

Instead of enumerating all seeds, sample the seeds by a pseudorandom sampler derived from the second source so that the number of rows is polynomial in the entropy; the resilient-function step is replaced by one that tolerates the resulting structured bad sets. The overhead is driven by the seed length of the non-malleable extractor.

## Depends on

- [Seeded non-malleable extractors (Dodis-Wichs)](seeded-non-malleable-extractors.md)

## Proof depends on

- [Chattopadhyay-Zuckerman: explicit two-source extractors for polylogarithmic min-entropy](explicit-two-source-extractors-for-polylogarithmic-entropy.md)

## Sources

- Avraham Ben-Aroya, Dean Doron, Amnon Ta-Shma, "An efficient reduction from two-source to non-malleable extractors: achieving near-logarithmic min-entropy", STOC (2017), SIAM Journal on Computing 48(2) (2019).
