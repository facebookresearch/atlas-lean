# Distance of a hypergraph product code

In the setting of the [dimension formula](dimension-of-a-hypergraph-product-code.md), let $d_i$ be the minimum distance of
the code $\ker H_i$ and $d_i^{T}$ that of the transpose code $\ker H_i^{T}$, with the convention that the minimum distance
of the zero code is $\infty$. The minimum distance $d$ of the [hypergraph product code](hypergraph-product-code.md)
satisfies

$$d \ge \min(d_1, d_2, d_1^{T}, d_2^{T}),$$

with equality when the minimum is attained by some $d_i$ with $d_{3-i} \ne \infty$, or by some $d_i^{T}$ with
$d_{3-i}^{T} \ne \infty$. In particular, if $H_1 = H_2 = H$ is the full-rank parity-check matrix of a code of length $m$
with positive rate and minimum distance $\Theta(m)$, the hypergraph product has $n = \Theta(m^2)$, $k = \Theta(n)$ and
$d = \Theta(\sqrt{n})$.

## Depends on

- [Hypergraph product code](hypergraph-product-code.md)

## Proof depends on

- [Dimension of a hypergraph product code](dimension-of-a-hypergraph-product-code.md)

## Sources

- J.-P. Tillich and G. Zémor, *Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength*, IEEE Trans. Inform. Theory 60 (2014), 1193–1202, arXiv:0903.0566, Section 5, Theorem 15 and Sections 5.1–5.2.
