# Weight covered at least n times

For a natural number $n$, a list $S$ of rows of natural numbers and a list
$w = (w_0, \dots, w_{m-1})$ of natural numbers (the weights), the weight covered at least $n$
times by $S$ is the sum of the weights $w_e$ over the elements $e < m$ with
$\sum_{r} r_e \ge n$, the sum running over the rows $r$ of $S$, counted with multiplicity, where
$r_e$ is entry $e$ of $r$, read as $0$ when $r$ has no entry $e$.
