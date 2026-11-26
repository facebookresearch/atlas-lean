# The CSS code of a chain complex

A chain complex of $\mathbb{F}_2$-vector spaces with chosen bases,

$$C_2 \xrightarrow{\ \partial_2\ } C_1 \xrightarrow{\ \partial_1\ } C_0, \qquad \partial_1 \partial_2 = 0,$$

defines a CSS code on $n = \dim C_1$ qubits (the basis of $C_1$) with $X$-checks the rows of $H_X = \partial_1$ and
$Z$-checks the rows of $H_Z = \partial_2^{T}$; the condition $\partial_1 \partial_2 = 0$ is $H_X H_Z^{T} = 0$, the
commutation of the checks. Conversely every CSS code arises this way. Logical $Z$-operators correspond to the homology
$H_1 = \ker \partial_1 / \operatorname{im} \partial_2$ and logical $X$-operators to the cohomology
$H^1 = \ker \partial_2^{T} / \operatorname{im} \partial_1^{T}$, the number of logical qubits is
$k = \dim H_1 = \dim H^1$, and the $Z$- and $X$-distances are the least Hamming weights of vectors representing nonzero
classes of $H_1$ and $H^1$; the [distance](../css-codes/distance-of-a-css-code.md) is their minimum. The toric code is the
cellular chain complex of the square tiling of the torus.

## Depends on

- [Distance of a CSS code](../css-codes/distance-of-a-css-code.md)

## Sources

- N. P. Breuckmann and J. N. Eberhardt, *Quantum low-density parity-check codes*, PRX Quantum 2 (2021), 040101, arXiv:2103.06309, Section II.B.1 (chain complexes, the correspondence $\partial_2 = H_Z^{tr}$, $\partial_1 = H_X$, logical operators as homology and cohomology, $k = \dim H_1(C)$).
