# One stack iteration of the one-hot generator

Let $L$ be a layout with $g$ symbol codes,
$K$ stacks and a label/state block of size $A$, let $T$, $H$, $t$, $k$ be natural numbers with
$t \le T$ and $k < K$, let $W = A + KHg$ be the row width of $L$ at height $H$, and let
$V = (T + 1)W$ be the number of variables. For $j < H$ let $B_j = tW + A + (kH + j)g$ be the
base of the cell at time $t$, stack $k$ and depth $j$, and let $w_j$ be the encoding of the
dense clause over $V$ variables with literals $(B_j + x, \mathrm{true})$ for
$x = 0, \dots, g - 1$ in increasing order, followed by the encodings of the dense clauses over
$V$ variables with literals $(B_j + x, \mathrm{false})$ and $(B_j + y, \mathrm{false})$ for all
pairs $x < y < g$, ordered by $y$ and then by $x$. Let $F$ be counter values whose scratch
counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are zero, with
$\mathrm{CB} = P = \mathrm{KB} = \mathrm{Hi} = 0$, $\mathrm{Vc} = V$, $\mathrm{Gc} = g$,
$\mathrm{HG} = Hg$, $\mathrm{Hs} = H$, $\mathrm{TW} = tW$ and $\mathrm{Kc} = k$. Then for every
output word $o$ and every machine state $v$, the generator of $L$ runs within the
one-stack-iteration step budget at $(g, K, H, V)$ from the label that starts the body of the
stack loop, with state $v$, counters $F$ and output $o$, to the head of the stack loop, with
state false, the same counters $F$, and output $w_0 w_1 \cdots w_{H-1}$ followed by $o$.
