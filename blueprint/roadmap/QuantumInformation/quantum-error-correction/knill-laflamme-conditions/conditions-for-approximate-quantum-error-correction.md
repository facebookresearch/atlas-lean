# Conditions for approximate quantum error correction

For channels $\mathcal{N}, \mathcal{M}$ let $d(\mathcal{N}, \mathcal{M}) = \max_\rho \sqrt{1 - F_\rho(\mathcal{N}, \mathcal{M})}$,
the Bures distance from the entanglement [fidelity](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/root-fidelity.md)
$F_\rho$ of the two channels on a purification of $\rho$. A code with encoding channel $\mathcal{E}$ is
*$\varepsilon$-correctable* under a noise [channel](../../quantum-operations/quantum-channel.md) $\mathcal{N}$ if some
recovery channel $\mathcal{R}$ has $d(\mathcal{R} \mathcal{N} \mathcal{E}, \mathrm{id}) \le \varepsilon$. A code with
projector $P$ is $\varepsilon$-correctable under $\mathcal{N}(\rho) = \sum_i E_i \rho E_i^{*}$ if and only if

$$P E_i^{*} E_j P = \lambda_{ij} P + P B_{ij} P$$

for the entries $\lambda_{ij}$ of some density operator and operators $B_{ij}$ with $d(\Lambda + \mathcal{B}, \Lambda) \le \varepsilon$,
where $\Lambda(\rho) = \sum_{ij} \lambda_{ij} \operatorname{Tr}(\rho) |j\rangle\langle i|$ and
$(\Lambda + \mathcal{B})(\rho) = \Lambda(\rho) + \sum_{ij} \operatorname{Tr}(\rho B_{ij}) |j\rangle\langle i|$ (on code states
$\Lambda + \mathcal{B}$ is the complementary channel $\rho \mapsto \sum_{ij} \operatorname{Tr}(E_i \rho E_j^{*}) |i\rangle\langle j|$ of
the noise, since $\operatorname{Tr}(E_i \rho E_j^{*}) = \operatorname{Tr}(\rho E_j^{*} E_i)$; with $|i\rangle\langle j|$ in both sums the
map need not be a channel), both regarded as
channels on states supported on the code, so that the maximum in $d$ ranges over code states $\rho = P \rho P$ (as in
Bény and Oreshkov, who apply their criterion to the noise composed with the encoding). For
$\varepsilon = 0$ this reduces to the [Knill–Laflamme conditions](is-correctable-iff-knill-laflamme.md). Choosing
$\lambda_{ij} = \operatorname{Tr}(\sigma E_i^{*} E_j)$ for any state $\sigma$ supported on the code ($\sigma = P \sigma P$,
equivalently $\sigma = V \tau V^{*}$ for the encoding isometry $V$ and a logical state $\tau$) gives a value of
$\varepsilon$ at most twice the optimal one. The support condition is needed: for the noise with Kraus operators $P$ and
$I - P$, which is the identity on the code, a state $\sigma$ supported on the orthogonal complement gives distance $1$,
not $0$.

## Expansion

A sound expansion adds pages for complementary channels (from a Stinespring dilation) and Bény and Oreshkov's Theorem 1,
which equates the optimal recovery distance $\min_{\mathcal{R}} d(\mathcal{R}\mathcal{N}, \mathcal{M})$ with the distance
between the complementary channels optimized over the environment side, proved with Uhlmann's theorem and a minimax
theorem; the corollary stated here follows from it, and the factor-two statement is their Corollary 3.

## Depends on

- [Quantum channel](../../quantum-operations/quantum-channel.md)
- [Fidelity of positive semidefinite matrices](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/root-fidelity.md)
- [The Knill–Laflamme conditions](is-correctable-iff-knill-laflamme.md)

## Sources

- C. Bény and O. Oreshkov, *General conditions for approximate quantum error correction and near-optimal recovery channels*, Phys. Rev. Lett. 104 (2010), 120501, arXiv:0907.5391, Definition 1, equation (5), Theorem 1 and Corollaries 2 and 3.
