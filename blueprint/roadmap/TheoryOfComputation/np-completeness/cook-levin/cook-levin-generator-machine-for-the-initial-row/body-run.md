# One phase-loop iteration of the initial-row generator

Let $L$ be a layout with $g$
symbol codes, let $ic, k_0 \in \mathbb{N}$, let $ycs$ be a list of $n$ certificate codes, and let
$p$ be a loop phase with base counter $c_Z(p)$ and loop-count counter $c_N(p)$. Let $F$ give the
value of each generator counter, with the scratch counters empty ($\mathrm{Rest}(F)$),
$F(\mathrm{CB}) = F(\mathrm{P}) = 0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(c_Z(p)) = Z$
and $F(c_N(p)) = t$. Suppose $t < N$ and $tg + Z \le V$, the clause kind of $p$ has strictly
increasing literal offsets, and all its literals at base $tg + Z$ lie below $V$. Then for every
output $o$ and flag $v$, the counter program of the generator runs in at most
$\mathrm{bodyB}(n + 2, g, N, V)$ steps from label $b_1(p)$ with flag $v$, counters $F$ and output
$o$ to the loop head of $p$ with flag false, counters $F$ and output
$\mathrm{encodeClause}(\mathrm{denseClause}(V, \mathrm{clits}(tg + Z, p)))$ followed by $o$.
Here $\mathrm{clits}(tg + Z, p)$ are the literals of the clause kind of $p$ at base $tg + Z$.
