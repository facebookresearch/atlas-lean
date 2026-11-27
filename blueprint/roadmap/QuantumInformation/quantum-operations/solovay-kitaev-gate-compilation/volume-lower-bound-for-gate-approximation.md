# Volume lower bound: logarithmic word length is necessary

For every finite $\mathcal{G} \subset \mathrm{SU}(d)$, if $\mathcal{G}_\ell$ is an $\varepsilon$-net then $\ell = \Omega\big((d^2 - 1)\log(1/\varepsilon) / \log |\mathcal{G}|\big)$. For gate sets of algebraic entries with spectral gap (for instance $\{H, T\}$ in $\mathrm{SU}(2)$ up to phases) word length $O(\log(1/\varepsilon))$ suffices non-constructively.

## Proof sketch

$|\mathcal{G}_\ell| \le |\mathcal{G}|^{\ell+1}$, and $\mathrm{SU}(d)$, a manifold of dimension $d^2 - 1$, needs $\Omega(\varepsilon^{-(d^2-1)})$ balls of radius $\varepsilon$ to be covered. The upper bound for spectrally gapped sets follows from equidistribution of random words (Harrow-Recht-Chuang) via the spectral gap of the averaging operator.

## Depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Sources

- Aram W. Harrow, Benjamin Recht, Isaac L. Chuang, "Efficient discrete approximations of quantum gates", Journal of Mathematical Physics 43 (2002); arXiv:quant-ph/0111031.
