# Gaussian-rational gates of the exact Toffoli decomposition

The one-qubit matrices

$$e^{i\pi/4} H = \tfrac{1 + i}{2} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}, \quad V = \sqrt X = \tfrac12 \begin{pmatrix} 1 + i & 1 - i \\ 1 - i & 1 + i \end{pmatrix}, \quad S = \begin{pmatrix} 1 & 0 \\ 0 & i \end{pmatrix}, \quad S^*, \quad X, \quad Z$$

and the two-qubit matrices SWAP, CNOT and controlled-$U$ for each $U$ above (in either control and target orientation) are unitary,
and all their entries lie in $\mathbb{Q}(i)$; so each two-qubit matrix, and each one-qubit matrix tensored with the $2 \times 2$ identity on a spectator qubit, is the entry matrix of a well-formed encoded 2-local gate on any pair of distinct qubits.
$V^2 = X$, $V V^* = I$, and $(e^{i\pi/4} H)^2 = i I$.

## Proof

Each matrix has entries in $\{0, \pm 1, \pm i, (\pm 1 \pm i)/2\}$. For $V$: the columns $\frac12(1+i, 1-i)$ and $\frac12(1-i, 1+i)$ have
squared norm $\frac14(2 + 2) = 1$ and inner product $\frac14((1-i)(1-i) + (1+i)(1+i)) = \frac14(-2i + 2i) = 0$; and $V^2 = \frac14 \begin{pmatrix} (1+i)^2 + (1-i)^2 & 2(1+i)(1-i) \\ 2(1-i)(1+i) & (1-i)^2 + (1+i)^2 \end{pmatrix} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. For $e^{i\pi/4}H$: $H$ is real orthogonal and
$\lvert (1+i)/\sqrt 2 \rvert = 1$. A controlled unitary is block diagonal with blocks $I$ and $U$, hence unitary.

## Depends on

- [Exact Gaussian-rational Toffoli and multi-controlled NOT decompositions](exact-2-local-gaussian-rational-toffoli-and-multi-controlled.md)
- [Encoded 2-local quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate.md)
- [Well-formed quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate-well-formed.md)

## Sources

- A. Barenco et al., *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457; arXiv:quant-ph/9503016, Lemma 6.1 (the gates $V$ with $V^2 = X$). <https://arxiv.org/abs/quant-ph/9503016>
