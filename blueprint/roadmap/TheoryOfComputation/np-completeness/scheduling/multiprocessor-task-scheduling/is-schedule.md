# Unit-slot schedules in MULTIPROCESSOR TASKS $P2 \mid \mathrm{intree}; p_i = 1; \mathrm{size}_i \mid \sum C_i$

For task sizes $\mathrm{size}_0, \dots, \mathrm{size}_{n-1}$ (one per listed entry) and a list $A$ of precedence arcs, natural-number start times $\sigma(j)$ form a schedule of the unit tasks when

- for every time slot $t \in \mathbb{N}$, the tasks with $\sigma(j) = t$ have total listed size at most $2$, and
- for every listed arc $(i, j)$, $\sigma(i) + 1 \le \sigma(j)$: task $j$ starts at or after task $i$ completes.

Each task occupies the single unit slot $[\sigma(j), \sigma(j) + 1)$ of the integer time line, so two tasks overlap in time exactly when they have the same start time, and the size test at equal start times is a capacity test on every slot. The arcs are read as listed, without a range or acyclicity test, and a listed size larger than $2$ makes the first condition fail.
