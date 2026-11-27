# Budgeted run

For a machine $M$, numbers $K, X \in \mathbb{N}$ and configurations $c$ and
$d$, the budgeted run from $c$ to $d$ with $K$ steps already spent and budget $X$ holds when there
is an $n \in \mathbb{N}$ with $K + n \le X$ such that $n$ steps of $M$ lead from $c$ to $d$.

It is used for goal-directed chaining of runs: the chaining lemmas only increase $K$.
