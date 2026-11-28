# Schedules in UNSAFE LOCKING POLICY for two distributed transactions

For an instance of UNSAFE LOCKING POLICY for two distributed transactions with transactions $T_0$ and $T_1$, a list $\sigma$ of pairs of natural numbers is a schedule when two tests hold:

- $\sigma$ is a permutation of the list of addresses $(0, p)$ for $p < |T_0|$ followed by $(1, p)$ for $p < |T_1|$, where $|T_t|$ is the number of steps of $T_t$; so it lists every step $(t, p)$ of both transactions exactly once and nothing else;
- for $t \in \{0, 1\}$ and every precedence pair $(a, b)$ of $T_t$, the position of the first occurrence of $(t, a)$ in $\sigma$ is less than that of $(t, b)$, where a pair that does not occur in $\sigma$ has position $|\sigma|$.

When the transaction is well formed, both ends of each precedence pair are steps of $T_t$, and the second test says that $(t, a)$ occurs before $(t, b)$ whenever step $a$ precedes step $b$ in $T_t$. Without well-formedness the second test is weaker: for example, if $T_0$ has one step, $T_1$ has none, and $T_0$ lists the precedence pair $(0, 1)$, then $\sigma = [(0, 0)]$ is a schedule, since the missing address $(0, 1)$ has position $1 > 0$.
