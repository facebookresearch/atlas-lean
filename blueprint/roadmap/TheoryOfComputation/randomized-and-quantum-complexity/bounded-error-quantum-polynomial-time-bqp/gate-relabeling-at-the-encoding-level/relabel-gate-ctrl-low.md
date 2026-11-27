# Relabelling a controlled gate on qubits 0 and 1

Matrices below have Gaussian-rational entries (complex numbers with rational real and imaginary
parts, each part encoded by a sign, a numerator and a denominator); $U_{\mathbb{C}}$ is the complex
matrix that $U$ represents. For a $2 \times 2$ Gaussian-rational matrix $U$ and a map $\pi$ on qubit
positions, relabelling the gate on qubits $0$ and $1$ whose entry list is the sixteen row-major
entries of controlled-$U$ with the first qubit as control gives, as an equality of encoded gates
(positions and entry lists), the controlled gate with control $\pi(0)$ and target $\pi(1)$: the
gate on $(\pi(0), \pi(1))$ with the same sixteen entries when $\pi(0) < \pi(1)$, and otherwise
the gate on $(\pi(1), \pi(0))$ whose entry list is the sixteen row-major entries of controlled-$U$
with the second qubit as control. Equality of decoded matrices alone is not enough: for the identity
relabelling, appending one entry leaves the matrix unchanged but changes the resulting encoded gate.
