# The one-hot generator

For a layout with label/state block size $A$, $K$ stacks and $g$
symbol codes, the program of a counter machine with an output bit stack and the unary counters
of the generator. Started with $T$ on the time counter $T_n$, $H$ on the height counter $H_s$ and
every other counter empty, it first sets $T_n = T + 1$, $G_c = g$, $HG = Hg$,
$W_c = A + K \cdot Hg$, $K_c = K$ and $V_c = (T + 1)W_c$. It then loops over times $t \le T$,
stacks $k < K$ and depths $j < H$; for each cell it computes the cell's base and pushes onto the
output stack the encodings of the cell's dense at-least-one and at-most-one clauses. When the
loops finish it halts.

On halting, the output stack holds the encoding of the one-hot cell family in front of its
original contents.
