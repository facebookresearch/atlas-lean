# Witness lookup

Given a list $N = (n_1, \dots, n_k)$ of natural numbers, a list
$w = (b_1, \dots, b_m)$ of booleans and a natural number $x$, the lookup of $x$ in $N$ and $w$ is
the timed computation (a returned boolean together with a natural-number cost) that scans the
pairs $(n_1, b_1), (n_2, b_2), \dots$ in order, charging one tick for each pair it examines, and
returns $b_i$ for the first $i$ with $n_i = x$; if either list runs out first, it returns false at
no further cost.

It is used with $N$ the variables occurring in a formula and $w$ the witness values, so the first
occurrence of a variable wins.
