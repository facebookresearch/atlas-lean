# Holley's condition for nested-wiring conditional measures, $q \ge 1$

Let $G = (V, E)$ be a finite simple graph, let $C \le C'$ be simple graphs on $V$ ($C$ a subgraph of $C'$), $0 < p < 1$, $q \ge 1$, $F$ a finite set of unordered pairs of vertices and $\psi$ an assignment of open/closed states to the unordered pairs of vertices. For all such assignments $a, b$,

$$\phi^C(a \mid F, \psi)\, \phi^{C'}(b \mid F, \psi) \le \phi^C(a \wedge b \mid F, \psi)\, \phi^{C'}(a \vee b \mid F, \psi),$$

where $\phi^C(\cdot \mid F, \psi)$ is the [conditional measure](cond-bc-prob.md) $\phi^{C}_{G,p,q}(\,\cdot \mid F, \psi)$, which gives $\omega$ the mass $w^C(\omega)/Z^C_{F,\psi}$ if $\omega$ agrees with $\psi$ on every unordered pair outside $F$ and $0$ otherwise, where $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ and $Z^C_{F,\psi}$ is the [sum of $w^C$ over the configurations agreeing with $\psi$ off $F$](induced-bc-z.md). Configurations are ordered coordinatewise (closed $<$ open), and $a \wedge b$, $a \vee b$ denote the coordinatewise minimum and maximum.
