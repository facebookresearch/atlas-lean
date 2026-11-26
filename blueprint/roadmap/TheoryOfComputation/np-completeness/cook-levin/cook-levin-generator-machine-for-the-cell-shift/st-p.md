# Block stages of the cell-shift generator

For a layout $L$ with label block size $A$ and
$K$ stacks, push-count and consumed-count tables $\mathrm{pl}$ and $\mathrm{cn}$, a number $N$ of
situations, a situation $i < N$ and a stack $k < K$, write $p = \mathrm{pl}(i, k)$ and
$c = \mathrm{cn}(i, k)$.
This assigns a statement of the generator to each setup or loop stage of block $(i, k)$; below,
"add $X$ to $Y$" copies counter $X$ onto $Y$ through the scratch counter $\mathrm{tmp}$ in two
stages, restoring $X$, and "drain $X$" empties $X$. The setup pushes $A$ units onto $\mathrm{KB}$,
adds $\mathrm{TW}$ to $\mathrm{KB}$, pushes $k$ units onto $\mathrm{Ka}$, adds
$\mathrm{Ka} \cdot \mathrm{HG}$ to $\mathrm{KB}$ by the multiplication routine (index
$\mathrm{md}$, scratch $\mathrm{tmp}$), drains $\mathrm{Ka}$, adds $\mathrm{Hs}$ to $\mathrm{U}$,
and goes to the label of the decrement chain for $\max(p, c)$. The pushed-fill stages add
$\mathrm{KB}$ and then $\mathrm{Wc}$ to $\mathrm{CW}$ and go to the entry label of the pushed-fill
chain for $p$; the fill drain drains $\mathrm{CW}$, and the next stage pushes $c - p$ units onto
$\mathrm{R}$ (truncated subtraction). The overflow loop pops $\mathrm{R}$, pushing each unit on
the index counter $\mathrm{Ri}$; for each popped unit it adds $\mathrm{U}$ and then $\mathrm{R}$ to
$\mathrm{Ka}$, adds $\mathrm{Ka} \cdot \mathrm{Gc}$ to $\mathrm{CB}$ by the multiplication
routine, drains $\mathrm{Ka}$ and runs the loop body with flag false; when $\mathrm{R}$ is empty it
moves $\mathrm{Ri}$ back onto $\mathrm{R}$. The in-range loop likewise pops $\mathrm{U}$ onto
$\mathrm{Ui}$ and runs the loop body with flag true for each popped unit, and when $\mathrm{U}$ is
empty moves $\mathrm{Ui}$ back onto $\mathrm{U}$. Finally it drains $\mathrm{U}$, $\mathrm{R}$ and
$\mathrm{KB}$ and goes to the entry label of the stack chain of situation $i$ for $k$.
