# Linear bounded automaton

A single-tape machine is a linear bounded automaton when it runs
in space $n + 1$ on inputs of length $n$: every configuration of its run on an input of length $n$
uses at most $n + 1$ cells, whether or not the run halts.

The input itself uses $\max(1, n)$ cells, and the extra cell lets the head step onto a blank cell
next to the input, the analogue of Sipser's endmarkers. With the bound $n$ instead, no machine
would qualify, since the empty input already uses one cell.
