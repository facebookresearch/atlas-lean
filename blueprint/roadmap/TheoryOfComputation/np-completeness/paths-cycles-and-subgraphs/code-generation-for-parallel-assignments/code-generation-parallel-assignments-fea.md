# Feasible CODE GENERATION FOR PARALLEL ASSIGNMENTS instances

An instance of CODE GENERATION FOR PARALLEL ASSIGNMENTS is feasible when some ordering $\pi$ of the $n$ assignments (position $i$ executes assignment $\pi(i)$, which writes $v_{\pi(i)}$; positions are $0$-based) has at most $K$ positions $i$ whose variable $v_{\pi(i)}$ lies in the operand set $B_{\pi(j)}$ of some later position $j > i$; a missing operand set is read as empty.
