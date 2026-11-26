# Optimal privacy amplification with an active adversary from non-malleable extractors

Two parties sharing a weak secret $X$ with $H_\infty(X) \ge k$ and communicating over a channel fully controlled by an active adversary can agree on a shared key of length $k - O(\log n + s)$ that is $2^{-s}$-close to uniform given the adversary's view (or detect tampering), using a two-round protocol whenever $k \ge C(\log n + s)$; the entropy loss and round complexity are asymptotically optimal.

## Proof sketch

Alice sends a uniform seed $Y$; Bob replies with $\mathrm{nmExt}(X, Y')$ for the received seed $Y'$ as an authentication tag together with a fresh seed. Non-malleability guarantees that if the adversary modified $Y$, the tag the adversary must forge is nearly uniform given its view, so tampering is detected; otherwise a strong extractor applied with Bob's seed yields the key. Li's optimal non-malleable extractors make all losses $O(\log n + s)$.

## Depends on

- [Li: seeded non-malleable extractors with asymptotically optimal seed length](seeded-non-malleable-extractors-with-optimal-seed-length.md)
- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Proof depends on

- [Li: seeded non-malleable extractors with asymptotically optimal seed length](seeded-non-malleable-extractors-with-optimal-seed-length.md)
- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- Yevgeniy Dodis, Daniel Wichs, "Non-malleable extractors and symmetric key cryptography from weak secrets", STOC (2009).
- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802.
