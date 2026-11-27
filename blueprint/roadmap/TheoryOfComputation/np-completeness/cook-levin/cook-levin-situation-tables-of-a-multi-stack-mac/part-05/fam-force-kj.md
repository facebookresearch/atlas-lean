# Transition clauses force the next label, stack-and-depth form

Let $L$ be a layout with
$K$ stacks and window depth $d$, let $\mathrm{la}, \mathrm{na} : \mathbb{N} \to \mathbb{N}$ and
$\mathrm{wa} : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be tables, and let $a$ be
an assignment satisfying the transition clause family of $L$, $\mathrm{la}$, $\mathrm{na}$ and
$\mathrm{wa}$ for bounds $T$, $H$ and $N$. Write $X[t, b]$ and $C[t, k, j, x]$ for the
label/state and cell variables at height $H$. If $t < T$, $i < N$, $X[t, \mathrm{la}(i)]$ is true
under $a$, and $C[t, k, j, \mathrm{wa}(i, k, j)]$ is true under $a$ for all $k < K$ and $j < d$,
then $X[t + 1, \mathrm{na}(i)]$ is true under $a$.
