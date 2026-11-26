# The integrality gap curve of the basic SDP

For a payoff family $\Lambda$ and $c \in [0,1]$, the **integrality gap curve** is

$$
S_\Lambda(c) = \inf\bigl\{\, \operatorname{opt}(\Im) \;:\; \Im \text{ an instance of } \mathrm{GCSP}(\Lambda) \text{ with } \operatorname{sdp}(\Im) \ge c \,\bigr\}.
$$

It is non-decreasing in $c$. An instance with $\operatorname{sdp}(\Im) \ge c$ and $\operatorname{opt}(\Im) \le s$ is a **$(c, s)$-integrality gap instance**.

## Depends on

- [The basic SDP relaxation of a generalized CSP](basic-sdp-relaxation.md)
- [Integrality gaps of linear programming relaxations](../../../ComputerScience/approximation-algorithms/lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Sources

- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
