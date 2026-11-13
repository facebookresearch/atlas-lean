# Sequencing

Let $P_u$, $P_s$ (update and situation definition), $P_h$ (shift), $P_a$
(accept) and $P_i$ (init) be generator programs that halt at their label `done`, and let $\xi$ be
a list of input codes. Suppose that for each generator $j \in \{u, s, h, a, i\}$ there are counter
values $F_j$, a word $w_j$ and a bound $B_j$ such that, for every output word $o$, the run of $P_j$
from its start label with state bit false, on stacks holding the counters $F_j$ and the output $o$
(for init, also $\xi$ on its input stack), reaches `done` within $B_j$ steps, with some state bit
and with output $w_j o$. Let $o$ be a word and let $S_0$ be host stacks whose output stack holds
$o$, whose input stack holds $\xi$, and whose private block of each generator $j$ holds the
counters $F_j$. Then the host program on $P_u, P_s, P_h, P_a, P_i$, started at the init
generator's start label with state bit false on $S_0$, reaches its final label within
$B_i + B_u + B_s + B_h + B_a + 5$ steps, with some state bit and with output
$w_a w_h w_s w_u w_i o$.
