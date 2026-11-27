# Raghavendra–Steurer: a generic rounding algorithm matching the gap curve

For every finite payoff family $\Lambda$ and every $\eta > 0$ there is a polynomial-time algorithm that, given an instance $\Im$ of $\mathrm{GCSP}(\Lambda)$ with $\operatorname{sdp}(\Im) \ge c$, outputs an assignment of value at least $S_\Lambda(c - \eta) - \eta$. The algorithm solves the basic SDP, projects the vectors onto a random low-dimensional subspace, discretizes, and solves the resulting constant-size instance by brute force.

## Proof sketch

Dimension reduction preserves inner products up to small error, which preserves the SDP value up to $\eta$. Discretizing the sphere to an $\eta$-net merges variables into a constant number of classes, giving a constant-size instance with SDP value at least $c - \eta$. By definition of $S_\Lambda$, this folded instance has an integral solution of value at least $S_\Lambda(c - \eta)$, found by brute force and unfolded.

## Depends on

- [The integrality gap curve of the basic SDP](integrality-gap-curve.md)
- [The basic SDP relaxation of a generalized CSP](basic-sdp-relaxation.md)
- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)

## Sources

- P. Raghavendra, D. Steurer, "How to round any CSP", FOCS (2009).
