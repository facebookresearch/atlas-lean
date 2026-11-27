# The basic SDP relaxation of a generalized CSP

For an instance $\Im$ of $\mathrm{GCSP}(\Lambda)$, the **basic SDP** has, for every variable $v$ and label $a \in [q]$, a vector $b_{v,a} \in \mathbb{R}^N$, and for every constraint $(P, v)$ a probability distribution $\mu_{P,v}$ on $[q]^k$, subject to

$$
\langle b_{v_i, a}, b_{v_j, c} \rangle = \Pr_{y \sim \mu_{P,v}}[y_i = a,\ y_j = c] \quad \text{for all } i, j \in [k],\ a, c \in [q],
$$

and $\sum_a b_{v,a}$ equal to a fixed unit vector. The SDP objective is $\operatorname{sdp}(\Im) = \mathbb{E}_{(P,v)} \mathbb{E}_{y \sim \mu_{P,v}} P(y)$. Always $\operatorname{sdp}(\Im) \ge \operatorname{opt}(\Im)$, and $\operatorname{sdp}(\Im)$ is computable to within any additive $\eta$ in time polynomial in $|\Im|$ and $\log(1/\eta)$. For Max-Cut it coincides with the Goemans-Williamson relaxation.

## Depends on

- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)
- [Objective of the MAX CUT semidefinite program](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/sdp-objective.md)
- [Feasible matrices of the MAX CUT semidefinite program](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/sdpfeasible.md)

## Sources

- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
- P. Raghavendra, D. Steurer, "How to round any CSP", FOCS (2009).
