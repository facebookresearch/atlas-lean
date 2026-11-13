# Correctness of the init generator, with its explicit time bound

Let $L$ be a layout with
$A$ label/state variables, $K$ stacks and $g > 0$ symbol codes, let $i_c < A$ and $k_0 < K$, and
let $Y$ be a strictly increasing list of codes with $0 < y < g$ for every $y \in Y$. Let $xs$ be a
list of codes below $g$ with $n = |xs|$, let $T, e, f$ be natural numbers with $f > 0$, and let
$o$ be a bit string. Start the generator for $L, i_c, k_0, Y$ at its start label with state false,
with the counters $\mathrm{Tn}, \mathrm{Xn}, \mathrm{En}, \mathrm{Fn}$ holding $T, n, e, f$ in
unary and all other counters empty, $o$ on the output stack, and $xs$ reversed on the input
stack. Then within $\mathrm{initBound}(L, |Y|, k_0, K - k_0 - 1, T, n, e, f)$ steps it reaches
the final label $\mathrm{done}$, and its output stack there is the bit encoding of the
layout-level init family for $L, i_c, k_0, Y, xs$, $m = n + e$, $T$ and $H = n + e + f$, followed
by $o$.
