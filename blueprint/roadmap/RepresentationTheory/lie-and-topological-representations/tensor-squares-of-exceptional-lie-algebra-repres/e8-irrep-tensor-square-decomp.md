# Tensor square of an irreducible $\mathfrak{e}_8$-representation of dimension $779247$

There exist a complex vector space $V$ and a representation of the exceptional Lie algebra
$\mathfrak{e}_8$ over $\mathbb{C}$ on $V$ such that $V$ has dimension $779247$ over $\mathbb{C}$,
$V$ is irreducible, and the tensor square $V \otimes_{\mathbb{C}} V$, with the representation
$x \cdot (v \otimes w) = (x \cdot v) \otimes w + v \otimes (x \cdot w)$ viewed as a module over the
universal enveloping algebra of $\mathfrak{e}_8$, has exactly $40$ isotypic components.

## Sources

- leanprover/lean-eval, commit 38361be, problem `e8_irrep_tensor_square_decomp`, https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/manifests/problems/e8_irrep_tensor_square_decomp.toml: the witness is $V(\omega_1 + \omega_8)$ (Bourbaki labelling), the unique irreducible representation of dimension $779247$, whose tensor square, computed with the LiE program, has $40$ distinct simple summands ($155$ counted with multiplicity).
