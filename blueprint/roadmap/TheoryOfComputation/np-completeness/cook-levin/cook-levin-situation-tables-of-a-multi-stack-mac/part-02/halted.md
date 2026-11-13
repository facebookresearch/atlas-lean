# Halted situations stay fixed

If the (label, state) pair decoded from the code
$\mathrm{la}(i)$ of situation $i$ has no label, so the machine has halted, then for every stack
number $k$ the next code equals the current one, $\mathrm{na}(i) = \mathrm{la}(i)$, and
$\mathrm{pl}(i, k) = 0$ and $\mathrm{cn}(i, k) = 0$: nothing is left pushed and nothing is
consumed.
