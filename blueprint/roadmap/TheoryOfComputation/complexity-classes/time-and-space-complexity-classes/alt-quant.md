# Alternating bounded quantifiers

Let $b : \mathbb{N} \to \mathbb{N}$ be a length bound,
$k$ a natural number, $R$ a Boolean function of a bitstring and a list of bitstrings, and $x$ a
bitstring. The statement with $k$ blocks, beginning with $\exists$ when the given flag is true and
with $\forall$ when it is false, is

$$Q_1 w_1 \, Q_2 w_2 \cdots Q_k w_k \; R(x, [w_1, \dots, w_k]) = \mathrm{true},$$

where the quantifiers $Q_1, \dots, Q_k$ alternate between $\exists$ and $\forall$ and every $w_i$
ranges over the bitstrings of length at most $b(|x|)$. For $k = 0$ it is
$R(x, []) = \mathrm{true}$.
