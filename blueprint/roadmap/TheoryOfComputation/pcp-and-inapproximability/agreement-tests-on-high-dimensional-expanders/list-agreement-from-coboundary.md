# Gotlib–Kaufman: list-agreement expansion from coboundary expansion

Let $X$ be a $d$-dimensional complex whose links are $\lambda$-local spectral expanders and which is a $\beta$-coboundary expander over every symmetric group $S_\ell$ in dimension $1$. Then $X$ is a **list-agreement expander**: for every assignment of $\ell$-element lists of local functions to top faces such that adjacent faces' lists are $\varepsilon$-close to matching in a consistent bijection on most edges, there exist $\ell$ global functions $G^1, \dots, G^\ell$ on $X(0)$ such that, for all but an $O(\varepsilon/\beta)$-fraction of top faces, the list on the face equals $\{G^1|_\sigma, \dots, G^\ell|_\sigma\}$.

## Proof sketch

The local bijections between lists on adjacent faces define an $S_\ell$-valued $1$-cochain on the face-adjacency complex; consistency on triangles means its coboundary is small. Coboundary expansion over $S_\ell$ makes the cochain close to a coboundary $h(u)h(v)^{-1}$, and relabelling each list by $h$ produces globally consistent sheets, from which the global functions are read off.

## Depends on

- [Non-abelian 1-cochains and unique-games coboundary expansion](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/nonabelian-cochain.md)
- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)

## Sources

- R. Gotlib, T. Kaufman, "List agreement expansion from coboundary expansion", ITCS (2023), arXiv:2210.15714.
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
