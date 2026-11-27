# The GKR delegation protocol: completeness and soundness

For a layered arithmetic circuit $C$ of depth $d$ and maximal layer width $2^{s}$ over $\mathbb{F}$, and an input $x$, the GKR protocol reduces a claim $\widetilde W_0(z_0)=v_0$ about the outputs, layer by layer, to a claim about $\widetilde W_d$, which the verifier checks directly from $x$. Each layer uses one sum-check protocol on the GKR identity over $2s$ variables of degree at most $2$ per variable, followed by a line-restriction step combining the two resulting claims into one. The honest prover is accepted with probability $1$ (perfect completeness), and if the claimed output is false then every prover is accepted with probability at most $O(d\,s/|\mathbb{F}|)$. For uniform circuits the verifier runs in time $O(n\log|\mathbb{F}|)+\mathrm{poly}(d,s,\log|\mathbb{F}|)$.

## Proof sketch

Completeness is immediate from the identity. For soundness, each sum-check round errs with probability at most (degree)$/|\mathbb{F}|$ by Schwartz–Zippel, and the line step errs with probability at most $s/|\mathbb{F}|$; a union bound over the $d$ layers and $O(s)$ rounds per layer gives the bound.

## Depends on

- [Layered arithmetic circuits and the GKR wiring identity](layered-arithmetic-circuits.md)
- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Proof depends on

- [The sum-check protocol](../the-sum-check-protocol.md)

## Sources

- Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum, "Delegating Computation: Interactive Proofs for Muggles", Journal of the ACM 62(4), Article 27, 2015.
- Justin Thaler, "Proofs, Arguments, and Zero-Knowledge", Foundations and Trends in Privacy and Security 4(2–4), 2022, Section 4.6 (soundness error $O(d\log S/|\mathbb{F}|)$).
