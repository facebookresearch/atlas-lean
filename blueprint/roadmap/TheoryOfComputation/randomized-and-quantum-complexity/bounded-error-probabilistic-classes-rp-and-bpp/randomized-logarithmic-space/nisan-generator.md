# Nisan's pseudorandom generator for space-bounded computation

For parameters $w,\ell$, Nisan's generator $G:\{0,1\}^{O(\ell\cdot w)}\to\{0,1\}^{w 2^{\ell}}$ is defined recursively from pairwise-independent hash functions $h_1,\dots,h_\ell:\{0,1\}^w\to\{0,1\}^w$ by $G_0(x)=x$ and $G_i(x;h_1,\dots,h_i)=G_{i-1}(x;h_1..h_{i-1})\,\|\,G_{i-1}(h_i(x);h_1..h_{i-1})$. For every machine with $2^{O(w)}$ configurations reading its random bits once in blocks of $w$ bits, the acceptance probability on $G$'s output differs from that on truly uniform bits by at most $2^{-\Omega(w)}$ (for $\ell=O(w)$). Consequently every $\mathsf{BPL}$ language is decided by a logspace machine whose random string has $O(\log^2 n)$ bits, and each output bit of $G$ is computable in space $O(\ell w)$.

## Proof sketch

Induct on the level: replacing the second half of independent blocks by the hashed copy is undetectable because, by the leftover-hash (mixing) lemma, pairwise-independent hashing preserves the joint distribution of the configuration reached after the first half and the second-half input, up to $2^{-\Omega(w)}$ per state transition, and the errors add up over $2^{\ell}$ levels of composition.

## Depends on

- [Randomized logarithmic space RL and BPL](rl-and-bpl.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Noam Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 1992.
