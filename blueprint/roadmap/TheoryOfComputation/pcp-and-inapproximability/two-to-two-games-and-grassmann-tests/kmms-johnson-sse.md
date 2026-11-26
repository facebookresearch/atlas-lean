# Khot–Minzer–Moshkovitz–Safra: small-set expansion in the Johnson graph

Let $J(n, \ell, t)$ be the Johnson graph on $\binom{[n]}{\ell}$ in which two sets are adjacent when their intersection has size $\ell - t$, with $\ell = o(n)$ and $t$ a constant fraction of $\ell$. For every $\delta > 0$ there are $r, \varepsilon > 0$ such that every set $S$ of vertices whose edge expansion is at most $1 - \delta$ has density at least $\varepsilon$ inside some zoom-in-zoom-out sub-family $\{A : I \subseteq A \subseteq W\}$ with $|I| + |[n] \setminus W| \le r$. This is the Johnson-scheme analogue of the Grassmann structure theorem used in the $2$-to-$2$ games theorem.

## Proof sketch

Fourier-analyse the indicator of $S$ in the Johnson scheme eigenspaces; small expansion forces substantial weight on low levels. A hypercontractive inequality for global functions on the slice converts low-level weight into large density on a restriction, and an induction on levels handles the remaining terms.

## Depends on

- [Zoom-in and zoom-out subgraphs of the Grassmann graph](grassmann-zoom.md)

## Proof depends on

- [Equivalence of Grassmann, shortcode and bilinear small-set expansion](shortcode-equivalence.md)
- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](../../../Combinatorics/boolean-functions/global-hypercontractivity-and-sharp-thresholds/kllm-global-hypercontractivity.md)

## Sources

- S. Khot, D. Minzer, D. Moshkovitz, M. Safra, "Small set expansion in the Johnson graph", ECCC TR18-078 (2018).
