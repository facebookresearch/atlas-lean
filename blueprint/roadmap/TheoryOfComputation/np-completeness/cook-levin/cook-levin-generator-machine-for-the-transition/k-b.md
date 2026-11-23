# Row offset of a literal in a transition clause

For a layout with $K$ stacks and window
depth $d$, the row offset $k_B(j)$ of literal $j$ is $0$ when $j \le Kd$ and $1$ when $j > Kd$.

Among the literals $0, \dots, Kd + 1$ of a transition clause it is $1$ only for the last one,
the next-label literal, which refers to the following time step.
