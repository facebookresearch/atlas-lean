# Unit-time open-shop schedules

For $m$ machines, $n$ jobs and a list $A$ of precedence arcs, natural-number start times $\sigma_k(j)$ of job $j$'s unit operation on machine $k$ form an open-shop schedule when

- on each machine $k$, the start times $\sigma_k(0), \dots, \sigma_k(n-1)$ are pairwise different,
- for each job $j$, the start times $\sigma_0(j), \dots, \sigma_{m-1}(j)$ are pairwise different, and
- for every listed arc $(i, j)$ and all machines $k, k'$, $\sigma_k(i) + 1 \le \sigma_{k'}(j)$: every operation of job $j$ starts at or after every operation of job $i$ completes.

Each operation occupies the single unit slot $[\sigma_k(j), \sigma_k(j) + 1)$ of the integer time line, so two operations overlap exactly when they start at the same time; on a real time line, different start times alone would not prevent overlap. Every one of the $m \cdot n$ operations takes one unit of time, whatever processing times an instance lists.
