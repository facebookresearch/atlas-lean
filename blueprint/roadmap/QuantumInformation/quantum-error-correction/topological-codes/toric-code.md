# Toric code

Let $L \ge 2$ and take the $L \times L$ square lattice on the torus (opposite sides of an $L \times L$ square identified):
$L^2$ vertices, $2L^2$ edges and $L^2$ faces. Put one qubit on each edge. For a vertex $s$ and a face $p$ let

$$A_s = \prod_{j \in \mathrm{star}(s)} X_j, \qquad B_p = \prod_{j \in \partial p} Z_j ,$$

where $\mathrm{star}(s)$ is the set of the four edges meeting $s$ and $\partial p$ the set of the four edges bounding $p$.
The toric code $\mathrm{TOR}(L)$ is the subspace of the $2L^2$ qubits fixed by every $A_s$ and every $B_p$; the
$A_s$ and $B_p$ are its check operators. Each check operator acts on four nearby qubits, which is why the code suits
local syndrome measurement. Codes on other cellulated surfaces (surface codes) are defined in the same way, with the supports
given by the cellular boundary matrices modulo $2$.

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version), equations (1)–(2) and Figure 1.
- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A.
