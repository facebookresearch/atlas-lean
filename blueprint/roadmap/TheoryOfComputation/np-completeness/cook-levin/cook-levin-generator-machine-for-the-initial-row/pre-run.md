# Run of the precomputation (initial-row generator)

Let $L$ be a layout with $K$ stacks,
let $i_c$ and $k_0$ be natural numbers and let $y$ be a list of certificate codes. For all natural
numbers $T, n, e, f$ and every output $o$, the counter part of the generator for $L$, $i_c$,
$k_0$, $y$ runs within $\mathrm{preB}(L, k_0, K - k_0 - 1, T, n, e, f)$ steps, the step bound for
the precomputation (with truncated subtraction), from the label $\mathrm{eg}$ of the first
precomputation part (its first stage), with flag false, the initial counters for $T, n, e, f$ and
output $o$, to the loop head of the tail phase, with flag false, the counters after the
precomputation for $L, k_0, T, n, e, f$ and output $o$.
