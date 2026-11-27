# Feasible instances of PRECEDENCE CONSTRAINED SCHEDULING

An instance $(l, m, P, D)$ is feasible when there are start times $\sigma(t) \in \mathbb{N}$ such that at every time $u$ at most $m$ tasks are running (task $t$ runs at times $u$ with $\sigma(t) \le u < \sigma(t) + l(t)$), every task finishes by $D$ ($\sigma(t) + l(t) \le D$), and $\sigma(t) + l(t) \le \sigma(t')$ whenever $(t, t') \in P$.
