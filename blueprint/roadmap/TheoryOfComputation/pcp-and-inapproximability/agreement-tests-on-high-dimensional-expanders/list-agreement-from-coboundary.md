# Gotlib–Kaufman: list-agreement expansion from coboundary expansion

Let $X$ be a $d$-dimensional simplicial complex that is a $1$-up agreement expander and whose **every link** (including the link of the empty face, i.e. $X$ itself) is a coboundary expander over the symmetric group $S_\ell$ in dimension $1$. Then Gotlib and Kaufman's local tester (Algorithm 4) is a **list-agreement test** for every **$2$-locally-differing** $k$-dimensional $\ell$-assignment on $X$ (an assignment of $\ell$-element lists of local functions to $k$-faces in which any two distinct functions in the same list differ on at least two vertices): its rejection probability is at least $\beta$ times the distance of the $\ell$-assignment to an agreeing (globally consistent) $\ell$-assignment, where $\beta > 0$ depends on $k$ as well as on the link coboundary-expansion and $1$-up agreement-expansion parameters (specifically $\beta = \frac{\alpha}{k}\cdot\frac{\eta}{2\eta+2}$ in Lemma 6.5; Gotlib–Kaufman, Definitions 2.24–2.25 and Theorem 6.1). Without the $2$-locally-differing distance assumption, list agreement cannot be tested with a constant number of queries (as shown by an odd-cycle obstruction).

## Proof sketch

Because every list is $2$-locally-differing, overlapping faces determine unique local bijections between their lists whenever they agree, defining an $S_\ell$-valued $1$-cochain across links. Coboundary expansion of every link over $S_\ell$ together with $1$-up agreement expansion ensures that small tester rejection probability forces the cochain to be close to a coboundary $h(u)h(v)^{-1}$, and relabelling each local list by $h$ glues the local lists into globally consistent sheets at distance bounded by a constant multiple (depending on $\beta$) of the rejection probability.

## Depends on

- [Non-abelian 1-cochains and unique-games coboundary expansion](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/nonabelian-cochain.md)
- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)

## Sources

- R. Gotlib, T. Kaufman, "List agreement expansion from coboundary expansion", ITCS (2023), arXiv:2210.15714.
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
