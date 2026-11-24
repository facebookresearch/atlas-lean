# Wired measure conditionally dominated by larger wirings, $q \ge 1$

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, let $C'$ be a simple graph on $V$ containing the boundary clique $K_\partial$ (the graph on $V$ whose edges are all pairs of distinct vertices of $\partial$), $0 < p < 1$, $q \ge 1$, $F$ a finite set of unordered pairs of vertices and $\psi$ an assignment of open/closed states to the unordered pairs of vertices. For every increasing (if $\omega \in A$ and $\omega \le \omega'$ coordinatewise, then $\omega' \in A$) set $A$ of configurations,

$$\sum_{\omega \in A} \phi^{K_\partial}(\omega \mid F, \psi) \le \sum_{\omega \in A} \phi^{C'}(\omega \mid F, \psi),$$

where $\phi^C(\cdot \mid F, \psi)$ is the [conditional measure](cond-bc-prob.md) $\phi^{C}_{G,p,q}(\,\cdot \mid F, \psi)$, which gives $\omega$ the mass $w^C(\omega)/Z^C_{F,\psi}$ if $\omega$ agrees with $\psi$ on every unordered pair outside $F$ and $0$ otherwise, where $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ and $Z^C_{F,\psi}$ is the [sum of $w^C$ over the configurations agreeing with $\psi$ off $F$](induced-bc-z.md).
