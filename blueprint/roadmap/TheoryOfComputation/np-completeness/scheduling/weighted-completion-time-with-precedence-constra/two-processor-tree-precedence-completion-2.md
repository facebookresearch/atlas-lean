# Feasible instances of TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME

An instance $(m, J, K, P)$ of TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME with task lengths $l(t)$, weights $w(t)$ and precedence relation $<$ is feasible when there is a schedule $\sigma$ assigning each task a start time $\sigma(t) \in \mathbb{N}$ such that

- at every time $u \in \mathbb{N}$ at most $m$ tasks run, where $t$ runs at $u$ when $\sigma(t) \le u < \sigma(t) + l(t)$;
- $t < t'$ implies $\sigma(t) + l(t) \le \sigma(t')$;
- the weighted completion time satisfies $\sum_t (\sigma(t) + l(t))\, w(t) \le K$.
