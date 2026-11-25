# Step bound for draining bounded stacks

Let $g, r, h \in \mathbb{N}$ and let $T$ assign
to every stack $k$ of the full machine (with alphabets $\Gamma_{g,r}$) a list $T_k$ of length at
most $h$. Let $L$ be the number of stacks other than the output stack. Then the drain step count
$1 + \sum_k (|T_k| + 1)$, summed over the stacks $k$ other than the output stack, is at most
$L(h + 1) + 1$.
