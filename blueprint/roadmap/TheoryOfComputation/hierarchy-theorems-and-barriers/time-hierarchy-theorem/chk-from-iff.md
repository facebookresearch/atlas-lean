# The cell-by-cell check recognizes code stacks

For all natural numbers $p_q, p_a$ and
every bit list $x$, the cell-by-cell check of $x$ from the key $(p_q, p_a)$ succeeds if and only
if there is a list of $m \ge 0$ entries $(q_1, a_1, q'_1, s_1), \dots, (q_m, a_m, q'_m, s_m)$ of
natural numbers such that $x$ is the concatenation of the cells of
$q_1, a_1, q'_1, s_1, \dots, q_m, a_m, q'_m, s_m$, in this order, and the keys $(q_i, a_i)$
strictly increase in lexicographic order, starting at $(p_q, p_a)$ or above. Here the cell of a
number $n$ is $n$ bits $\mathrm{true}$ followed by one bit $\mathrm{false}$.
