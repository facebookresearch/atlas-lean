# Agreement tests for ensembles of local functions

Let $\mathcal{F}$ be a family of $k$-element subsets of a ground set $[n]$, endowed with a distribution, and $\Sigma$ an alphabet. A **local ensemble** is a collection $\{f_s : s \to \Sigma\}_{s \in \mathcal{F}}$. An **agreement test** is a distribution $\mathcal{D}$ on pairs $(s_1, s_2) \in \mathcal{F}^2$ with $s_1 \cap s_2 \ne \emptyset$; the test accepts when $f_{s_1}|_{s_1 \cap s_2} = f_{s_2}|_{s_1 \cap s_2}$. Its **acceptance probability** is

$$
\operatorname{Agr}_{\mathcal{D}}(\{f_s\}) = \Pr_{(s_1, s_2) \sim \mathcal{D}}\bigl[f_{s_1}|_{s_1 \cap s_2} = f_{s_2}|_{s_1 \cap s_2}\bigr].
$$

The ensemble is **$\eta$-close to global** if some $G : [n] \to \Sigma$ satisfies $\Pr_{s}[f_s = G|_s] \ge 1 - \eta$. When $\Sigma = \{0,1\}$ and $f_s$ is viewed as an element of $\{0,1\}^k$, the task is called **direct product testing**.

## Depends on

- [Pure weighted simplicial complexes and their face distributions](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/pure-weighted-complex.md)

## Sources

- O. Goldreich, S. Safra, "A combinatorial consistency lemma with application to proving the PCP theorem", SIAM Journal on Computing 29 (2000) 1132-1154.
- I. Dinur, D. Steurer, "Direct product testing", CCC (2014), ECCC TR13-179.
- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
