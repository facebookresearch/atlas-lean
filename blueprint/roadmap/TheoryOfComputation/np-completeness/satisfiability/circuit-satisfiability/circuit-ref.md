# Resolving a circuit input

Given an assignment $x = (x_0, \dots, x_{n-1})$ of booleans to
the variables and the list $v = (v_0, \dots, v_{k-1})$ of the values of the gates evaluated so
far, an input index $r$ resolves to $x_r$ if $r < n$, to $v_{r-n}$ if $n \le r < n + k$, and to
false if $r \ge n + k$.
