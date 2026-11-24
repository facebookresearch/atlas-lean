# A one-qubit unitary embedded on the second qubit is a well-formed gate

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. Matrices below have
Gaussian-rational entries (complex numbers with rational real and imaginary parts, each part encoded
by a sign, a numerator and a denominator); $U_{\mathbb{C}}$ is the complex matrix that $U$
represents. Let $U$ be a $2 \times 2$ Gaussian-rational matrix with
$U_{\mathbb{C}}^\dagger U_{\mathbb{C}} = I$, and let $i < j < N$. The gate on qubits $i$ and $j$
whose entry list encodes $I_2 \otimes U_{\mathbb{C}}$ is well-formed on $N$ qubits.
