# Step bound for the main loop

For every bit string $l$, whether or not a clause is open, and
all natural numbers $n, k, m, Q$ with $|l| + n + k + m \le Q$, the exact step count of the main loop
on stash $l$ with literal, slot and clause counters $n, k, m$ is at most
$(|l| + 1)(2Q + 6) + Q + 4$.
