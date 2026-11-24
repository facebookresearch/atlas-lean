# Poles of L-functions and nonvanishing of global theta lifts

This node is still to be broken down. It covers Yamana's criterion, combined with the tower property of global theta
lifting, as Gan, Qiu and Takeda use it in their proof of the Rallis inner product formula. Let $\pi$ be a cuspidal
automorphic representation of the symplectic or unitary group $G(U_n)$, and, in the notation of Gan–Qiu–Takeda, let
$V_r$ be an $\epsilon$-Hermitian space with character $\chi_{V_r}$, $d(n)$ and $s_{m,n}$ as there, and
$\Theta_{n, V}(\pi)$ the [global theta lift](global-theta-lifts.md) of $\pi$ to $H(V)$.

- **Theorem** (Yamana, with the tower property). If $L(s + \tfrac12, \pi \times \chi_{V_r})$ is not holomorphic at
  $s = s_{m,n}$, then there is an $\epsilon$-Hermitian space $V^\#$ with $\chi_{V^\#} = \chi_{V_r}$ and
  $\dim V_r + \dim V^\# = 2\, d(n)$ such that $\Theta_{n, V^\#}(\pi) \ne 0$.

## Expansion

A good expansion has a statement page for Yamana's Theorem 10.1 (2) in his own formulation, after reading S. Yamana,
"L-functions and theta correspondence for classical groups", and a page deducing the form above through the tower
property, citing the sources below with locators; the statement above is the one Gan, Qiu and Takeda use.

## Depends on

- [Global theta lifts of cusp forms](global-theta-lifts.md), for $\Theta_{n, V}(\pi)$ and the tower property

## Proof depends on

- [Global theta lifts of cusp forms](global-theta-lifts.md), for the tower property of global theta lifting

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and the Rallis inner
  product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3, TeX source): the proof of
  Theorem 11.4 (ii), TeX lines 4232–4241 ("By [Y4, Theorem 10.1 (2)] and the tower property of global theta lifting, if
  the $L$-function ... is not holomorphic at $s = s_{m,n}$, then there exists an $\epsilon$-Hermitian space $V^\#_{r'}$ with
  $\chi_{V^\#_{r'}} = \chi_{V_r}$ and $\dim V_r + \dim V^\#_{r'} = 2 \cdot d(n)$ such that the global theta lift ... is
  non-vanishing"), for $G(U_n)$ symplectic or unitary.
- S. Yamana, "L-functions and theta correspondence for classical groups", Invent. Math. 196 (2014), 651–732,
  Theorem 10.1 (2), as cited by Gan, Qiu and Takeda ([Y4]).
