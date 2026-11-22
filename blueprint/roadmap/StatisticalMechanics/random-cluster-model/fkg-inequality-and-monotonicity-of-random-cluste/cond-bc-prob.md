# Conditional random-cluster measure with a boundary wiring

Let $G = (V, E)$ be a finite simple graph, $C$ a simple graph on $V$, $p, q \in \mathbb{R}$, $F$ a finite set of unordered pairs of vertices, and $\psi$ an assignment of open/closed states to the unordered pairs of vertices. The conditional measure gives an assignment $\omega$ the mass

$$\phi^C(\omega \mid F, \psi) = \begin{cases} w^C(\omega) / Z^C_{F,\psi} & \text{if } \omega(e) = \psi(e) \text{ for every pair } e \notin F, \\ 0 & \text{otherwise,} \end{cases}$$

where $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ is the [weight with boundary wiring $C$](bc-weight.md) and $Z^C_{F,\psi}$ is the [sum of $w^C$ over the configurations agreeing with $\psi$ off $F$](induced-bc-z.md) (the quotient is read as $0$ if $Z^C_{F,\psi} = 0$). When $0 \le p \le 1$, $q > 0$ and $Z^C_{F,\psi} > 0$ (always the case when $0 < p < 1$ and $q > 0$), this is the conditional distribution of the [random-cluster probability with boundary wiring $C$](bc-prob.md) given agreement with $\psi$ off $F$; when $Z^C_{F,\psi} = 0$, which can happen for $p \in \{0, 1\}$, it is the zero function.
