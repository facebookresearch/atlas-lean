# Optimal privacy amplification with an active adversary from non-malleable extractors

Two parties sharing a weak secret $X$ with $H_\infty(X) \ge k$ and communicating over a channel fully controlled by an active adversary can agree on a shared key that is $2^{-s}$-close to uniform given the adversary's view (or detect tampering) with an explicit two-round protocol: there is a constant $0<\alpha<1$ such that for all $n,k$ and every security parameter $s\le\alpha k$, the protocol has entropy loss $O(\log\log n+s)$, so the key has length $k-O(\log\log n+s)$, and communication complexity $O(\log n+s)$. These parameters are asymptotically optimal for $s$ up to $\Omega(k)$.

## Proof sketch

Alice sends a uniform seed $Y$. Bob receives $Y'$, computes the MAC key $R'=\mathrm{nmExt}(X,Y')$, chooses a fresh seed $W'$ for a strong seeded extractor, and sends $W'$ together with the tag $\mathrm{MAC}_{R'}(W')$ of a one-time message authentication code; the extractor output $\mathrm{nmExt}(X,Y')$ itself is never sent. Alice receives $(W,T)$, recomputes $R=\mathrm{nmExt}(X,Y)$, and accepts only if $T=\mathrm{MAC}_R(W)$; after verification both parties output $\mathrm{Ext}(X,W)$. If the adversary modified $Y$, non-malleability makes $R$ nearly uniform given $R'$ and the adversary's view, so a forged tag is rejected except with small probability; if $Y$ is unmodified, $R=R'$ is close to uniform given $Y$ and one-time MAC security protects $W'$. The MAC authenticates a seed of $\Omega(\log n)$ bits, so its key has $O(\log\log n+s)$ bits, which bounds the entropy loss, while sending the seeds costs $O(\log n+s)$ communication; Li's optimal non-malleable extractors achieve these bounds.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Li: seeded non-malleable extractors with asymptotically optimal seed length](seeded-non-malleable-extractors-with-optimal-seed-length.md)
- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- Yevgeniy Dodis, Daniel Wichs, "Non-malleable extractors and symmetric key cryptography from weak secrets", STOC (2009), doi:10.1145/1536414.1536496.
- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802 (Theorem 1.13).
