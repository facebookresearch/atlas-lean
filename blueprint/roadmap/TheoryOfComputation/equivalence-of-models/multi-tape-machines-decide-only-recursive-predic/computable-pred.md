# A predicate decided by a multi-tape machine is computable

Let $\alpha$ be a primcodable
type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive
recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-tape machine, then $p$ is
computable, that is, $p$ is decidable and its Boolean characteristic function
$\alpha \to \mathrm{Bool}$ is computable.

This is Post's theorem applied to $p$ and its complement, both recursively enumerable.
