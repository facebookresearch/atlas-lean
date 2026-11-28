# Feasible instances of TOTAL DISCREPANCY

An instance of TOTAL DISCREPANCY, with tasks $t$ listed as pairs $(l_t, M_t)$ of natural numbers and a natural bound $k$, is feasible when some real starting times $s_t$ (negative ones allowed) form a [one-processor schedule](is-schedule.md) and

$$
\sum_t \left| s_t + \frac{l_t}{2} - M_t \right| \le k,
$$

that is, the total distance between the actual midtimes $s_t + l_t / 2$ and the preferred midtimes $M_t$ is at most $k$. Feasibility does not include [well-formedness](well-formed.md); the decision problem requires both.
