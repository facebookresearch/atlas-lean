# Alternating projections estimate the acceptance probability of a fixed witness

Let $V$ be a verifier circuit acting on a witness register $\mathsf{W}$ and an ancilla register initialized to $|0^m\rangle$, let $\Delta = I_{\mathsf{W}} \otimes |0^m\rangle\langle 0^m|$ and $\Pi = V^\dagger (|1\rangle\langle 1|_{out} \otimes I) V$. Let $Q = (I \otimes \langle 0^m|) \Pi (I \otimes |0^m\rangle)$ on $\mathsf{W}$ with spectral decomposition $Q = \sum_j p_j |\psi_j\rangle\langle\psi_j|$. Starting from $|w\rangle|0^m\rangle$ and alternately measuring $\{\Pi, I - \Pi\}$ and $\{\Delta, I - \Delta\}$ for $N$ rounds produces outcomes $y_1, \dots, y_{2N}$ such that the number of indices $i \le 2N - 1$ with $y_i = y_{i+1}$ is distributed as the mixture $\sum_j |\langle w | \psi_j\rangle|^2 \, \mathrm{Bin}(2N - 1, p_j)$ (with the convention that the initial state counts as outcome $\Delta$).

## Proof sketch

By Jordan's lemma the two projections $\Delta$ and $\Pi$ decompose the space into invariant subspaces of dimension at most two, in each of which they are rank-one projections at angle $\theta_j$ with $\cos^2 \theta_j = p_j$, spanned by $|\psi_j\rangle|0^m\rangle$ and its image under $\Pi$. Inside one block, alternating measurements form a two-state Markov chain whose transitions repeat the last outcome with probability $p_j$ independently. Expanding $|w\rangle$ in the eigenbasis of $Q$ gives the mixture.

## Depends on

- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
