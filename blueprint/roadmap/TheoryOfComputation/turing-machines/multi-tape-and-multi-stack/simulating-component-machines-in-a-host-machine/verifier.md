# Verifier host

Let $c$ be a component machine with stacks $c_X \ne c_W$, maps $g_X$ and
$g_W$ from bits to the alphabets of $c_X$ and $c_W$, and labels $\mathit{start}$, $\mathit{yes}$
and $\mathit{no}$ with $\mathit{yes} \ne \mathit{no}$, where the program halts at $\mathit{yes}$
and at $\mathit{no}$. Let $f$ assign a boolean to each pair of bit lists and let $p$ be a
polynomial with natural number coefficients. Suppose that for all bit lists $x$ and $w$, the
component started at $\mathit{start}$ with state false, the bits of $x$ mapped by $g_X$ on $c_X$,
the bits of $w$ mapped by $g_W$ on $c_W$ and every other stack empty reaches the label
$\mathit{yes}$ if $f(x, w)$ is true and $\mathit{no}$ otherwise within $p(|x| + |w|)$ steps. Then
the verifier host machine computes $(x, w) \mapsto f(x, w)$ in polynomial time, with the verifier
host's step bound for $p$ as time bound: on the pair encoding of $(x, w)$, over the pair alphabet,
it outputs the one-element bit list $[f(x, w)]$.
