# Multi-purpose machine flow-shop schedules

For $n$ jobs with processing times $p_{i,s}$ at stages $s$, start times $\sigma_{i,s}$ and machines $a_{i,s} \in \{0, \dots, m-1\}$ form a multi-purpose machine flow-shop schedule when each operation $(i, s)$ runs on a machine of $\mu_s$, operation $(i, s+1)$ starts no earlier than operation $(i, s)$ completes, and two different operations on the same machine occupy disjoint time intervals $[\sigma_{i,s}, \sigma_{i,s} + p_{i,s})$.
