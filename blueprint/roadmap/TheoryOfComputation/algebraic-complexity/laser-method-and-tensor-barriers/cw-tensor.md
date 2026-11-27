# The Coppersmith–Winograd tensor

For an integer $q \ge 1$, the **Coppersmith-Winograd tensor** $\mathrm{CW}_q$ in $\mathbb{F}^{q+2} \otimes \mathbb{F}^{q+2} \otimes \mathbb{F}^{q+2}$ with basis indices $\{0, 1, \dots, q+1\}$ is

$$
\mathrm{CW}_q = \sum_{i=1}^{q}\bigl(x_0 y_i z_i + x_i y_0 z_i + x_i y_i z_0\bigr) + x_0 y_0 z_{q+1} + x_0 y_{q+1} z_0 + x_{q+1} y_0 z_0.
$$

Partitioning each index set as $\{0\} \cup \{1, \dots, q\} \cup \{q+1\}$ (blocks $0, 1, 2$), $\mathrm{CW}_q$ is a sum of six **constituent** subtensors indexed by block triples $(I, J, K)$ with $I + J + K = 2$, each isomorphic to a matrix multiplication tensor: $\langle 1, 1, q \rangle$ (three rotations) and $\langle 1, 1, 1 \rangle$ (three rotations).

## Depends on

- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)
- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)

## Sources

- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
