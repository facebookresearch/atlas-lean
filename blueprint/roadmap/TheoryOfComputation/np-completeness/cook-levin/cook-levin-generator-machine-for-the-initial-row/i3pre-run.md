# Counter part of one I3 iteration

Let $L$ be a layout with $g$ symbol codes. Suppose the
counters $F$ of the init generator's counter part have $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$,
$c_2$ and $\mathrm{CB}$ equal to $0$, $\mathrm{Gc} = g$, $\mathrm{ZA} = Z$ and
$\mathrm{Xn} = r + 1$. Then for every output $o$ and flag $v$, the counter part, started at the
head of the I3 loop with flag $v$, counters $F$ and output $o$, reaches the first read test (the
halting label if $g = 0$) in at most $1 + (2Z + 2) + (r(2g + 3) + r + 2)$ steps, with flag false,
output $o$, and the counters of $F$ except that $\mathrm{Xn} = r$ and $\mathrm{CB} = rg + Z$.
