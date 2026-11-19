# Pauli operator $X^a Z^b$ on $n$ qubits

For $a, b \in \mathbb{F}_2^n$, the Pauli operator $X^a Z^b$ is the matrix on $\mathbb{C}^{\mathbb{F}_2^n}$
sending the basis state $|v\rangle$ to $(-1)^{b \cdot v} |v + a\rangle$. It applies phase flips
$Z$ ($|0\rangle \mapsto |0\rangle$, $|1\rangle \mapsto -|1\rangle$) on the qubits in the support of
$b$, then bit flips $X$ ($|0\rangle \leftrightarrow |1\rangle$) on the qubits in the support of
$a$. It acts on the qubits in the union of the two supports.

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III, the discussion of bit and phase errors after equation (9).
