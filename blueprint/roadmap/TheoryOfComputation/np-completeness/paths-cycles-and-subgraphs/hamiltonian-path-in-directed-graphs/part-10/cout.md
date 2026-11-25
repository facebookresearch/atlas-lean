# Exit labels of the counter comparisons

The label the verifier goes to after comparing
two counters, where $a$ is the current vertex, $b$ the previous one, $c$ the number of vertices
seen, $n$ the number of vertices and $s$, $t$ the two ends: after comparing $a$ with $n$ it goes
to the head-or-edge dispatch if $a < n$; after comparing $a$ with $s$ it goes to the repeat scan
if $a = s$; after comparing $c$ with $n$ it goes to the nonzero-count check if $c = n$; after
comparing $b$ with $t$ it goes to the accept label if $b = t$; in every other case it goes to
the reject label.
