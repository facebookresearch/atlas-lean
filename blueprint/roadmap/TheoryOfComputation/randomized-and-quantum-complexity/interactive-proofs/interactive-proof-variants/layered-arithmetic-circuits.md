# Layered arithmetic circuits and the GKR wiring identity

A **layered arithmetic circuit** over a field $\mathbb{F}$ of depth $d$ has layers $0$ (outputs) to $d$ (inputs) with $S_j=2^{s_j}$ gates in layer $j$; each gate of layer $j< d$ is an addition or multiplication gate of two gates of layer $j+1$. Let $W_j:\{0,1\}^{s_j}\to\mathbb{F}$ give the gate values, $\widetilde W_j$ its multilinear extension, and $\widetilde{\mathrm{add}}_j,\widetilde{\mathrm{mult}}_j$ the multilinear extensions of the wiring predicates. Then for all $z\in\mathbb{F}^{s_j}$,

$$
\widetilde W_j(z)=\sum_{b,c\in\{0,1\}^{s_{j+1}}}\widetilde{\mathrm{add}}_j(z,b,c)\bigl(\widetilde W_{j+1}(b)+\widetilde W_{j+1}(c)\bigr)+\widetilde{\mathrm{mult}}_j(z,b,c)\,\widetilde W_{j+1}(b)\,\widetilde W_{j+1}(c).
$$

The circuit family is **uniform** if the wiring extensions are evaluable in time $\mathrm{poly}(s_j,\log|\mathbb{F}|)$.

## Proof sketch

Both sides are multilinear in $z$ and agree on $z\in\{0,1\}^{s_j}$, where the wiring predicates select the two inputs of gate $z$; a multilinear polynomial is determined by its values on the cube.

## Depends on

- [Multilinear extension of a Boolean function](../../../hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum, "Delegating Computation: Interactive Proofs for Muggles", Journal of the ACM 62(4), Article 27, 2015.
- Justin Thaler, "Proofs, Arguments, and Zero-Knowledge", Foundations and Trends in Privacy and Security 4(2–4), 2022, Section 4.6 (the identity for $\widetilde W_j$).
