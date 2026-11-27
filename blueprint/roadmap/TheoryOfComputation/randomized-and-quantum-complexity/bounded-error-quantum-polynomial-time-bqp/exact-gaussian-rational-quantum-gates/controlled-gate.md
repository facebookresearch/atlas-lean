# Controlled gate on a control and a target qubit

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. Matrices below have
Gaussian-rational entries (complex numbers with rational real and imaginary parts, each part encoded
by a sign, a numerator and a denominator); $U_{\mathbb{C}}$ is the complex matrix that $U$
represents. For a $2 \times 2$ Gaussian-rational matrix $U$ and qubit positions $c$ (control) and
$t$ (target), the controlled gate is $(c, t, e)$, with $e$ the entry list of controlled-$U$ with the
first qubit of the pair as control, when $c < t$; otherwise it is $(t, c, e')$, with $e'$ the entry
list of controlled-$U$ with the second qubit as control. The positions are in nondecreasing order, and the second branch is used when $c = t$: then the result $(c, c, e')$ is an encoding, but not a well-formed gate on any number of qubits.
