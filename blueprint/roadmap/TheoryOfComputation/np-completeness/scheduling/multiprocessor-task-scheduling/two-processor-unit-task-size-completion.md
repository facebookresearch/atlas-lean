# Feasible instances of MULTIPROCESSOR TASKS $P2 \mid \mathrm{intree}; p_i = 1; \mathrm{size}_i \mid \sum C_i$

An instance $(\mathrm{sizes}, A, K)$ is feasible when some natural-number start times $\sigma$ form a [unit-slot schedule](is-schedule.md) of the listed tasks for the arcs $A$ and have total completion time

$$
\sum_j (\sigma(j) + 1) \le K.
$$

Feasibility does not include [well-formedness](well-formed-4.md); the decision problem requires both.
