# Step bound for the precomputation

For a layout $L$ with $A$ label/state variables, $K$
stacks and $g$ symbol codes, and numbers $k_0, q, T, n, e, f$, write $h = n + e + f$. The bound is

$$
1 + (2n + 2) + (2e + 2) + (2(n + e) + 2) + (2f + 2) + (h(2g + 3) + h + 2) + 1 + 1 +
(K(2hg + 3) + K + 2) + (K + 1) + 1 + ((T + 1)(2(Khg + A) + 3) + (T + 1) + 2) + 1 + 1 +
(k_0(2hg + 3) + k_0 + 2) + (k_0 + 1) + (2(k_0 hg + A) + 2) + (n(2g + 3) + n + 2) +
(2(k_0 hg + A) + 2) + ((n + e)(2g + 3) + (n + e) + 2) + 1 + (2(k_0 hg + A) + 2) + (2hg + 2) +
1 + (k_0(2h + 3) + k_0 + 2) + (k_0 + 1) + 1 + (q(2h + 3) + q + 2) + (q + 1).
$$

The precomputation uses it with $q = K - k_0 - 1$.
