# The GKR delegation protocol: completeness and soundness

For a layered arithmetic circuit $C$ of size $S$, depth $d$ and maximal layer width $2^{s}$ over $\mathbb{F}$, and an input $x$ of length $n$, the GKR protocol reduces a claim $\widetilde W_0(z_0)=v_0$ about the outputs, layer by layer, to a claim about $\widetilde W_d$, which the verifier checks directly from $x$. Each layer uses one sum-check protocol on the GKR identity over $2s$ variables of degree at most $2$ per variable, followed by a line-restriction step combining the two resulting claims into one. The honest prover is accepted with probability $1$ (perfect completeness), and if the claimed output is false then every prover is accepted with probability at most $O(d\log(S)/|\mathbb{F}|)$. For log-space uniform circuits the verifier runs in time $O(n+d\cdot\mathrm{polylog}(S))$.

## Proof sketch

Completeness is immediate from the identity. For soundness, a false claim forces some round in which the prover's univariate polynomial differs from the prescribed one yet agrees with it at the verifier's random point: in a sum-check round both have degree $O(1)$, so this happens with probability $O(1/|\mathbb{F}|)$, and in a line-restriction step (at most $d$ of them) both have degree $O(\log S)$, probability $O(\log(S)/|\mathbb{F}|)$; a union bound over all rounds gives the bound.

Derived width-based form (not stated in the cited sources): measuring by the layer width, each line-restriction polynomial has degree at most $s$, so the soundness error is $O(d\,s/|\mathbb{F}|)$ with $s=\log_2$ of the maximal layer width, and the verifier time is $O(n\log|\mathbb{F}|)+\mathrm{poly}(d,s,\log|\mathbb{F}|)$ bit operations.

## Depends on

- [Layered arithmetic circuits and the GKR wiring identity](layered-arithmetic-circuits.md)
- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Proof depends on

- [The sum-check protocol](../the-sum-check-protocol.md)

## Sources

- Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum, "Delegating Computation: Interactive Proofs for Muggles", Journal of the ACM 62(4), Article 27, 2015.
- Justin Thaler, "Proofs, Arguments, and Zero-Knowledge", Foundations and Trends in Privacy and Security 4(2–4), 2022, Section 4.6.5 ("The soundness error of the GKR protocol is $O(d\log(S)/|\mathbb{F}|)$") and Table 4.4 (verifier time $O(n + d\cdot\mathrm{polylog}(S))$ for log-space uniform layered arithmetic circuits of size $S$ and depth $d$); author's copy dated July 18, 2023.
