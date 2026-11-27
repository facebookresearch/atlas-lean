# Goldwasser–Sipser set lower-bound protocol with perfect completeness

Let $S\subseteq\{0,1\}^{N}$ be a set whose membership has polynomial-time verifiable certificates, and let an integer $K$ with $1\le K\le 2^{N}$ be given. There is a constant-round public-coin protocol with perfect completeness: for a suitable power $S^\ell$ with $\ell=O(\log N)$, Merlin sends pairwise-independent hash functions $h_1,\dots,h_m:\{0,1\}^{N\ell}\to\{0,1\}^{k}$, Arthur sends a uniformly random target $y\in\{0,1\}^k$, and Merlin replies with an index $i$ and an element of $S^\ell$, with certificates, that $h_i$ maps to $y$. If $|S|\ge K$ Merlin can choose the $h_i$ so that the images $h_i(S^\ell)$ cover $\{0,1\}^k$, so Arthur accepts with probability $1$; if $|S|\le K/2$ every Merlin strategy is accepted with probability at most a constant $c<1$. By the round collapse, which preserves perfect completeness, the same holds for a two-message protocol in which Arthur moves first.

In the basic Goldwasser–Sipser protocol, where Arthur himself picks one random hash function $h:\{0,1\}^N\to\{0,1\}^k$ with $2^{k-2}\le K\le2^{k-1}$ and a target, completeness is not perfect: some choices of $h$ miss the target.

## Proof sketch

For a fixed target, $m$ independent pairwise-independent hash functions all miss it with probability at most $(2^k/|S|^\ell)^m$ by the second-moment bound, so with $2^k\approx K^\ell/2$ and $m>k$ a union bound over the $2^k$ targets shows that a covering choice exists when $|S|\ge K$. When $|S|\le K/2$ the union of the images has at most $m(K/2)^\ell\le 2^{k+1}m2^{-\ell}$ elements, a constant fraction of $\{0,1\}^k$ once $2^\ell\gg m$, which $\ell=O(\log N)$ achieves.

## Depends on

- [Public-coin Arthur–Merlin games with a fixed move pattern](arthur-merlin-move-patterns.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Proof depends on

- [Babai–Moran: AM[k] = AM for every constant k](am-round-collapse.md)

## Sources

- Shafi Goldwasser and Michael Sipser, "Private Coins versus Public Coins in Interactive Proof Systems", Proceedings of the 18th Annual ACM Symposium on Theory of Computing, 59–68, 1986.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 8 (Section 8.4.1 and Chapter 8, Exercise 3 of the January 2007 web draft: "a perfectly complete AM[O(1)] protocol for proving a lower bound on set size", with the hint to cover $\{0,1\}^k$ by hashed images of $S^\ell$).
- Martin Fürer, Oded Goldreich, Yishay Mansour, Michael Sipser and Stathis Zachos, "On Completeness and Soundness in Interactive Proof Systems", Advances in Computing Research 5, 1989 (perfect completeness for Arthur–Merlin games).
