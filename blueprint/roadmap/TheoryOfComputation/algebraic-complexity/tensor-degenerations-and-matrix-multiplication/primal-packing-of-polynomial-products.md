# Pass's primal packing of polynomial products

Let $c,t,a,b\ge1$ with $ct\ge a+2b-1$. Then the $c+1$ full products $\mathrm{Full}_{a,b}$ of one polynomial $A$ of length $a$ with polynomials $P_1,\dots,P_{c+1}$ of length $b$, together with one middle product of $A$ with a polynomial $Q$, are obtained as a degeneration (modulo $\varepsilon$) from $c$ full products of $A$ with the encoded polynomials $E_\nu=P_\nu-z^tP_{\nu+1}+\varepsilon z^bQ^{(\nu)}$, where $Q^{(\nu)}$ is the $\nu$-th block of $t$ consecutive coefficients of $Q$: a "$(c+1)$-for-$c$" packing with a shared left input.

## Proof sketch

The telescoping sum $\sum_\nu z^{t\nu}AE_\nu=AP_1+\varepsilon z^bAQ-z^{ct}AP_{c+1}$ exposes the middle coefficients of $AQ$ at order $\varepsilon$, and the products $AP_\nu$ are recovered from consecutive differences because the condition $ct\ge a+2b-1$ prevents overlaps of coefficient ranges.

## Depends on

- [Polynomial multiplication tensors](polynomial-multiplication-tensors.md)
- [Tensor restrictions and degenerations](tensor-restrictions-and-degenerations.md)

## Sources

- Rafael Pass, "Matrix Multiplication from Polynomial Packings: A Constructive and Elementary Proof of ω ≤ 9/4", arXiv:2610.28627, 2026.
