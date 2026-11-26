# The toric code check operators commute

For the [toric code](toric-code.md) on the $L \times L$ torus, every vertex operator $A_s$ commutes with every face
operator $B_p$, because $\mathrm{star}(s)$ and $\partial p$ share either $0$ or $2$ edges; vertex operators commute among
themselves, and so do face operators. Moreover

$$\prod_{s} A_s = I, \qquad \prod_{p} B_p = I ,$$

since every edge lies in exactly two stars and in exactly two face boundaries, and $X^2 = Z^2 = I$.

## Depends on

- [Toric code](toric-code.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version) (the paragraph after equation (1) and the paragraph after equation (2)).
- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A.
