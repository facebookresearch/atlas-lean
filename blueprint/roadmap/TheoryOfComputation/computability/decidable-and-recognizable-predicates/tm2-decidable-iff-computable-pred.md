# Multi-stack decidable predicates are exactly the computable predicates

Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is decidable by a multi-stack machine if and
only if it is computable, that is, $p$ is decidable and its Boolean characteristic function
$\alpha \to \mathrm{Bool}$ is computable.
