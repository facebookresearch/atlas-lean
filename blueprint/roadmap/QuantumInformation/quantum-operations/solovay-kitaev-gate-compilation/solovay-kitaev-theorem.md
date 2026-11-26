# Solovay-Kitaev theorem

Let $\mathcal{G} \subset \mathrm{SU}(d)$ be a universal gate set. There is a constant $C = C(\mathcal{G})$ such that for every $\varepsilon \in (0, 1/2)$, $\mathcal{G}_\ell$ is an $\varepsilon$-net for

$$
\ell = C \log^{c}(1/\varepsilon), \qquad c = \frac{\log 5}{\log(3/2)} \approx 3.97 .
$$

Moreover a word of this length approximating a given $U$ within $\varepsilon$ can be computed in time $O(\log^{2.71}(1/\varepsilon))$ from a precomputed net of constant accuracy.

## Proof sketch

By density and compactness, $\mathcal{G}_{\ell_0}$ is an $\varepsilon_0$-net for some constant $\ell_0$. Recursively, given an $\varepsilon_{k}$-approximation $U_k$ of $U$, decompose $U U_k^{-1}$, which lies within $\varepsilon_k$ of $I$, as a balanced commutator of $V, W$ at distance $O(\sqrt{\varepsilon_k})$ from $I$; approximate $V, W$ to accuracy $\varepsilon_k$ recursively and use the commutator error lemma to get accuracy $\varepsilon_{k+1} = O(\varepsilon_k^{3/2})$. Word length multiplies by $5$ per level and accuracy improves by the power $3/2$, giving the exponent $\log 5/\log(3/2)$.

## Depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Proof depends on

- [Balanced group commutator decomposition near the identity](balanced-group-commutator-decomposition.md)
- [Approximate commutators of near-identity unitaries are quadratically accurate](error-of-approximate-group-commutators.md)

## Sources

- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030.
- Alexei Kitaev, Alexander Shen, Mikhail Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, AMS (2002).
