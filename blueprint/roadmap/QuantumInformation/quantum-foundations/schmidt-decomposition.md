# Schmidt decomposition

Let $\mathcal{X}$ and $\mathcal{Y}$ be finite-dimensional complex Hilbert spaces. Every unit vector
$u \in \mathcal{X} \otimes \mathcal{Y}$ can be written as

$$u = \sum_{i=1}^r \sqrt{p_i}\, x_i \otimes y_i$$

with $r \le \min(\dim\mathcal{X}, \dim\mathcal{Y})$, positive numbers $p_1, \dots, p_r$ summing to $1$, and
orthonormal families $\{x_i\}$ in $\mathcal{X}$ and $\{y_i\}$ in $\mathcal{Y}$. The $p_i$ are the nonzero
eigenvalues of both reduced states of $uu^*$, which therefore have the same nonzero spectrum.

## Depends on

- [Left partial trace of a rank-one matrix](../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-left-vec-mul-vec-star.md)
- [Right partial trace of a rank-one matrix](../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right-vec-mul-vec-star.md)
- [Density matrices, pure states and reduced states](../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 3.8.1 (the decomposition, for
  finite-dimensional Hilbert spaces) and (11.26) in the proof of Theorem 11.2.1 (the reduced states). <https://arxiv.org/pdf/1106.1445v8>
