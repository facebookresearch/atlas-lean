# Affine hash families give retention channels

Let $p$ be a prime and let $h_{a,b}(v)=a v+b \bmod p$ with $(a,b)$ uniform in $\mathbb{F}_p^2$. For a rate $f$ and a set $V\subseteq\mathbb{F}_p$, the channel that retains $v$ iff $h_{a,b}(v)<\lceil f p\rceil$ retains each vertex with probability within a factor $2$ of $f$, retains any two distinct vertices independently (pairwise independence), and therefore satisfies the conditional rarity bound used by column detectors: for every set $U$ of vertices, the probability that more than $k$ retained vertices of $U$ have large incoming weight is at most $O(f\,|U|/k)$. Stage channels with moduli $p_l\le 2\,q^{l}|V|$ can be chosen for every level of the hierarchy.

## Proof sketch

Pairwise independence of affine hashing over a prime field gives exact first and second moments of retained counts; Chebyshev's or Markov's inequality on these counts gives the rarity bounds.

## Depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026.
- J. Lawrence Carter and Mark N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
