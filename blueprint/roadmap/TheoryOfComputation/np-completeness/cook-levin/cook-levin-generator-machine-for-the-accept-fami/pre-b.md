# Cost of the precomputation of the accept generator

For a layout $L$ with $A$
label/state variables per row, $K$ stacks and $g$ symbol codes, and for $k_1, T, H \in \mathbb{N}$,
let $W = A + KHg$ be the row width. The step budget of the precomputation is
$3 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + (T(2W + 3) + T + 2) + 1 +
((T + 1)(2W + 3) + (T + 1) + 2) + (2TW + 2) + 2 + (k_1(2Hg + 3) + k_1 + 2)$.
