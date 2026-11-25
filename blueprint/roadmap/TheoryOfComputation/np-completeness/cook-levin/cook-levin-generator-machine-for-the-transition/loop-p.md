# Time-loop invariant of the transition-family generator

Let $L$ be a layout with
label/state block size $A$, $K$ stacks and $g$ symbol codes, let $T, H \in \mathbb{N}$, and write
$W = A + KHg$ for the number of variables per time step and $V = (T + 1)W$ for the total number of
variables. Counter values $f$ of the generator satisfy the time-loop invariant when the scratch
counters $\mathrm{Q}$, $\mathrm{Ka}$, $\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$
are all $0$, $f(\mathrm{P}) = 0$, $f(\mathrm{TW}) = 0$, $f(\mathrm{HG}) = Hg$,
$f(\mathrm{Wc}) = W$ and $f(\mathrm{Vc}) = V$.

The counters $\mathrm{Tn}$, $\mathrm{Ti}$, $\mathrm{Hs}$ and $\mathrm{Gc}$ are not constrained.
