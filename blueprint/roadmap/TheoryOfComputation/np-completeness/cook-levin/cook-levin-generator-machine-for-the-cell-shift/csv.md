# Constant offset of a literal in a block

Let $L$ be a layout with $K$ stacks, $g$ symbol
codes and window depth $d$, let $N \in \mathbb{N}$ be the number of situations, and let
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$ and $\mathrm{pu}$ give the situation offsets, push
counts, consumed counts and pushed codes. For a situation $i < N$, a stack $k < K$, a clause kind
$c$ with parameters $g$ and $d$, and $l \in \mathbb{N}$, the constant offset of literal $l$ of $c$
in block $(i, k)$ is the constant offset of literal $l$ of $c$ with situation offset
$\mathrm{sa}(i)$, push count $\mathrm{pl}(i, k)$, consumed count $\mathrm{cn}(i, k)$ and pushed
codes $j \mapsto \mathrm{pu}(i, k, j)$.
