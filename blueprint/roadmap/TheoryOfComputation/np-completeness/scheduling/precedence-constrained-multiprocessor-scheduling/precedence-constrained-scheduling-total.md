# Feasible instances of PRECEDENCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME

An instance $(l, m, P, K)$ is feasible when there are start times $\sigma(t)$ such that at every time $u$ at most $m$ tasks are running (task $t$ runs at times $u$ with $\sigma(t) \le u < \sigma(t) + l(t)$), $\sigma(t) + l(t) \le \sigma(t')$ whenever $(t, t') \in P$, and $\sum_t (\sigma(t) + l(t)) \le K$.
