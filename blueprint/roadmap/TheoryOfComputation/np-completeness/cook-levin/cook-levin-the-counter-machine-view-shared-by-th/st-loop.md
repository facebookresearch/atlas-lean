# A runtime `for` loop in the counter view

Let $M$ be a counter machine, let $c \ne c_d$
be counters, and let $\mathrm{head}$, $\mathrm{body}$, $\mathrm{rest}$, $\mathrm{next}$ be labels
such that at $\mathrm{head}$, $M$ pops a unit from $c$, then pushes a unit onto $c_d$ and goes to
$\mathrm{body}$, or goes to $\mathrm{rest}$ if $c$ was empty; and at $\mathrm{rest}$, $M$ pops a
unit from $c_d$, then pushes a unit onto $c$ and stays at $\mathrm{rest}$, or goes to
$\mathrm{next}$ if $c_d$ was empty. Each of these pops sets the flag to true if a unit was popped
and to false if the stack was empty, and the pushes leave the flag unchanged. Let
$n, B \in \mathbb{N}$, let $\mathrm{blk}$ assign a list of Booleans to each natural number, and
let $f$ be counter values with $f(c) = n$ and $f(c_d) = 0$; for $t < n$ write $g_t$ for the
counter values that agree with $f$ except that $g_t(c) = t$ and $g_t(c_d) = n - t$, and write
juxtaposition of lists for concatenation. Suppose that for every $t < n$ and every list $o$ of
Booleans, $M$ goes in at most $B$ steps from label $\mathrm{body}$, flag true and stacks
$\mathrm{st}(g_t, o)$ to label $\mathrm{head}$, some flag and stacks
$\mathrm{st}(g_t, \mathrm{blk}(t)\, o)$. Then for every flag $v$ and every list $o$ of Booleans,
$M$ goes in at most $n(B + 1) + n + 2$ steps from label $\mathrm{head}$, flag $v$ and stacks
$\mathrm{st}(f, o)$ to label $\mathrm{next}$, flag false and stacks
$\mathrm{st}(f, \mathrm{blk}(0)\, \mathrm{blk}(1) \cdots \mathrm{blk}(n-1)\, o)$.

The body runs with $c$ holding $t = n - 1, \dots, 0$ in that order, so the blocks end up in
ascending order.
