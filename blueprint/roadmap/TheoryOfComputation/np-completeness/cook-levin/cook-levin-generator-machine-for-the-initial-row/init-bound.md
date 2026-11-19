# Time bound of the init generator

Let $L$ be a layout with $A$ label/state variables,
$K$ stacks and $g$ symbol codes, and let $n_Y, k_0, q, T, n, e, f$ be natural numbers. Put
$H = n + e + f$ and let $V = (T + 1)(A + K H g)$ be the number of variables. The bound is the
[precomputation step bound](pre-b.md) for $L, k_0, q, T, n, e, f$, plus $6$ times the [phase-loop step bound](loop-b.md) for $n_Y + 2, g, K H + H, V$, plus the [clause step bound](clause-b.md) for $n_Y + 2, V$.

The generator uses it with $q = K - k_0 - 1$.
