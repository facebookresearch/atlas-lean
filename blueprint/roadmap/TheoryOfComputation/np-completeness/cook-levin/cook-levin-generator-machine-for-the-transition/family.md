# The transition clause family

Fix a layout with label block size $A$, $K$ stacks, $g$
symbol codes and window depth $d$, tables $\mathrm{la}, \mathrm{na} : \mathbb{N} \to \mathbb{N}$
and $\mathrm{wa} : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$, and
$T, H, N \in \mathbb{N}$. Let $W = A + KHg$, let $X[t, a]$ be the variable $tW + a$, and let
$C[t, k, j, x]$ be the variable $tW + A + (kH + j)g + x$. The family is the CNF formula that
lists, for each time $t < T$ and within it each situation $i < N$, the dense clause over
$(T + 1)W$ variables built from the literal list $\neg X[t, \mathrm{la}(i)]$, then
$\neg C[t, k, j, \mathrm{wa}(i, k, j)]$ for $k < K$ and $j < d$ in lexicographic order, then
$X[t + 1, \mathrm{na}(i)]$.
