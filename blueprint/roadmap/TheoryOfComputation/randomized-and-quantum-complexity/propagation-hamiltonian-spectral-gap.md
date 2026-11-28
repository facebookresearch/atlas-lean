# Propagation Hamiltonian spectral gap

Let $T \ge 1$ and let the propagation Hamiltonian be
$H_{\mathrm{prop}} = \sum_{t=1}^{T} \tfrac12 \bigl(I \otimes (\lvert t \rangle\langle t \rvert + \lvert t-1 \rangle\langle t-1 \rvert) - U_t \otimes \lvert t \rangle\langle t-1 \rvert - U_t^* \otimes \lvert t-1 \rangle\langle t \rvert\bigr)$.
Conjugating by the unitary $W = \sum_{t=0}^{T} U_t \cdots U_1 \otimes \lvert t \rangle\langle t \rvert$ gives
$W^* H_{\mathrm{prop}} W = I \otimes \tfrac12 L_{T+1}$, where $L_{T+1}$ is the combinatorial Laplacian of the path with $T+1$ vertices;
each subspace spanned by $U_t \cdots U_1 \lvert \psi \rangle \otimes \lvert t \rangle$, $t = 0, \dots, T$, for a fixed $\psi$ is invariant.
The eigenvalues of $\tfrac12 L_{T+1}$ are $1 - \cos(\pi k/(T+1))$ for $k = 0, \dots, T$, so the smallest nonzero one is
$1 - \cos(\pi/(T+1)) \ge 2/(T+1)^2$, because $1 - \cos x \ge 2x^2/\pi^2$ for $0 \le x \le \pi$. For example, $T = 1$ gives $1$. Without the factor $\tfrac12$ the eigenvalues double.

## Depends on

- [Unitary evolution and elementary gates](../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Related topics

- [Applying a 2-local gate to a state](../complexity-classes/time-and-space-complexity-classes/apply-gate.md)

## Sources

- J. Kempe, A. Kitaev and O. Regev, "The complexity of the local Hamiltonian problem", arXiv:quant-ph/0406180v2, Section 4, equation (2) and Claim 2 with its proof (the change of basis $W$ and the block matrix (4)). <https://arxiv.org/abs/quant-ph/0406180>
- A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer, 2012 (author copy), §1.4.4 (the Laplace spectrum of the path $P_n$ is $2 - 2\cos(\pi j/n)$, $j = 0, \dots, n-1$). <https://www.win.tue.nl/~aeb/2WF02/spectra.pdf>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §14.3 (the terms $H_t$ with the factor $\tfrac12$). <https://arxiv.org/pdf/1907.09415v6>
