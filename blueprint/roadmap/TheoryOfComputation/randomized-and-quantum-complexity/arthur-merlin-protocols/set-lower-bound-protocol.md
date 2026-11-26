# Goldwasser–Sipser set lower-bound protocol with perfect completeness

Let $S\subseteq\{0,1\}^{N}$ be a set whose membership has polynomial-time verifiable certificates, and let $K\le 2^{N}$ be given. There is a two-message public-coin protocol (Arthur sends random hash functions and a target, Merlin replies with an element and its certificate) such that if $|S|\ge K$ then Arthur accepts with probability $1$ (for every random string Merlin has an accepted reply), and if $|S|\le K/2$ then Arthur accepts with probability at most a constant $c<1$.

## Proof sketch

Start from the Goldwasser–Sipser protocol, in which Arthur sends a random pairwise-independent hash function and target and Merlin exhibits a certified element of $S$ hashing to the target. Run polynomially many hash functions in parallel and accept if Merlin succeeds for one of them; the Lautemann covering argument makes the hashed images of a large $S$ cover every target, giving perfect completeness, while for $|S|\le K/2$ a union bound over the hash functions bounds the acceptance probability.

## Depends on

- [Public-coin Arthur–Merlin games with a fixed move pattern](arthur-merlin-move-patterns.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Shafi Goldwasser and Michael Sipser, "Private Coins versus Public Coins in Interactive Proof Systems", Proceedings of the 18th Annual ACM Symposium on Theory of Computing, 1986.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 8, Exercise 3.
