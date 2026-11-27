# Feasible MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH OUT-TREE PRECEDENCE AND UNIT TIMES TO MINIMIZE MAXIMUM LATENESS instances

An instance is feasible when some multipurpose-machine schedule (start times $\sigma$ and
machine assignment $a$ that form a valid schedule of the operations) obeys the precedence arcs,
each operation of a predecessor job finishing before any operation of its successor starts, and
has lateness at most $y = y^+ - y^-$: every operation $t$ of job $j$ satisfies
$\sigma_t + p_t + y^- \le d_j + y^+$, where a due date missing from the list counts as $0$.
