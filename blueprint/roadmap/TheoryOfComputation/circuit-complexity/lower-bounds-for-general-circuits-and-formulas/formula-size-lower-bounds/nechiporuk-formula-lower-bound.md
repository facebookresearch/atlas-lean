# Nechiporuk's formula lower bound

Let $Y_1,\dots,Y_k$ be disjoint sets of variables of a Boolean function $f$ and let $s_i(f)$ be the number of distinct subfunctions of $f$ on $Y_i$. Every formula over a basis of fan-in at most two computing $f$ with leaf size $L$ satisfies $\prod_{i=1}^k s_i(f)\le 2^{4L+k}$; hence

$$
L\ge\frac14\sum_{i=1}^k\log_2 s_i(f)-\frac k4 .
$$

For element distinctness on $m$ blocks of $2\log_2 m$ bits ($n=2m\log_2 m$ variables), each block has at least $\binom{m^2}{m-1}$ subfunctions, so every formula over the full binary basis has leaf size $\Omega(m^2\log m)=\Omega(n^2/\log n)$.

## Proof sketch

Apply Nechiporuk's lemma to each block $Y_i$ with $\ell_i$ leaves, where $\sum\ell_i\le L$: $s_i\le 2\cdot16^{\ell_i}$. Multiply.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Nechiporuk's subfunction counting lemma](nechiporuk-subfunction-counting-lemma.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady, 1966.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
