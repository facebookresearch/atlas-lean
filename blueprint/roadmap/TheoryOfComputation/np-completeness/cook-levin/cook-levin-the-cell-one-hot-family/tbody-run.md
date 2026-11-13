# Generator run over one time step

Let $L$ be a layout with $A$ label/state variables per
row, $K$ stacks and $g$ symbol codes, let $t \le T$ and $H$ be natural numbers, and write
$W = A + K H g$ for the row width, $V = (T + 1) W$ for the number of variables and $p_i$ for the
variable with index $i$. Let $F$ assign a value to each counter of the one-hot generator such
that the scratch counters are empty ($\mathrm{Rest}(F)$),
$F(CB) = F(P) = F(KB) = F(TW) = F(Hi) = F(Kd) = 0$, $F(Vc) = V$, $F(Gc) = g$, $F(HG) = H g$,
$F(Hs) = H$, $F(Wc) = W$, $F(Kc) = K$ and $F(Tn) = t$. For $k < K$ and $j < H$ let
$b_{k,j} = t W + A + (k H + j) g$ be the base of cell $(k, j)$, and let $E_{k,j}$ be the encoding
of the CNF formula consisting of the dense clause over $V$ variables with the positive literals
$p_{b_{k,j}}, \dots, p_{b_{k,j} + g - 1}$, followed, for $y = 0, \dots, g - 1$ in turn and within
each for $x = 0, \dots, y - 1$ in turn, by the dense clause over $V$ variables whose only literals
are $\lnot p_{b_{k,j} + x}$ and $\lnot p_{b_{k,j} + y}$. Let $E$ be the concatenation of the
$E_{k,j}$ for $k = 0, \dots, K - 1$ and within each for $j = 0, \dots, H - 1$. Then for every
output list $o$ and every flag $v$, the one-hot generator of $L$, started at the first label of
the stage computing $TW := t W$ with flag $v$, output stack $o$ and each counter $c$ holding
$F(c)$, reaches within the time-step budget of $L$, $T$ and $H$ (T Body B) steps the head of the
time loop with flag false, the same counters, and output stack $E \, o$ (concatenation).
