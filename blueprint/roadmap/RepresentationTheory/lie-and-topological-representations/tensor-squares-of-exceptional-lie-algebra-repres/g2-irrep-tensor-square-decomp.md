# Tensor square of an irreducible $\mathfrak{g}_2$-representation of dimension $64$

There exist a complex vector space $V$ and a representation of the exceptional Lie algebra
$\mathfrak{g}_2$ over $\mathbb{C}$ on $V$ such that $V$ has dimension $64$ over $\mathbb{C}$,
$V$ is irreducible, and the tensor square $V \otimes_{\mathbb{C}} V$, with the representation
$x \cdot (v \otimes w) = (x \cdot v) \otimes w + v \otimes (x \cdot w)$ viewed as a module over the
universal enveloping algebra of $\mathfrak{g}_2$, has exactly $14$ isotypic components.

## Sources

- leanprover/lean-eval, commit 38361be, problem `g2_irrep_tensor_square_decomp`, https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/manifests/problems/g2_irrep_tensor_square_decomp.toml: the witness is the irreducible representation $V(\omega_1 + \omega_2)$, and the decomposition of its tensor square, computed with the LiE program, is $V(0,0) + V(1,0) + 2V(0,1) + 2V(2,0) + 2V(1,1) + 2V(0,2) + 3V(3,0) + 3V(2,1) + V(1,2) + V(0,3) + 2V(4,0) + 2V(3,1) + V(2,2) + V(5,0)$, with $14$ distinct summands.
