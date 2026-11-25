# One step of the weighted tardy jobs computation

Let $J$ be a list of jobs, each a triple
$(p, d, w)$ of natural numbers (processing time, due date, weight). Given a state $(t, s)$ and a
natural number $j$, let $(p, d, w)$ be the job at position $j$ of $J$, counting from $0$, or
$(0, 0, 0)$ if $J$ has no position $j$, and let $t' = t + p$. The step returns $(t', s + w)$ if
$d < t'$, and $(t', s)$ otherwise.
