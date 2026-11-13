# The verifier host's run

Let $c$ be a component machine with stacks $c_X \ne c_W$, maps
$g_X$ and $g_W$ from bits to the alphabets of $c_X$ and $c_W$, and labels $\mathit{start}$,
$\mathit{yes}$ and $\mathit{no}$ with $\mathit{yes} \ne \mathit{no}$, where the program halts at
$\mathit{yes}$ and at $\mathit{no}$. Let $f$ assign a boolean to each pair of bit lists and let
$p$ be a polynomial with natural number coefficients. Suppose that for all bit lists $x$ and $w$,
the component started at $\mathit{start}$ with state false, the bits of $x$ mapped by $g_X$ on
$c_X$, the bits of $w$ mapped by $g_W$ on $c_W$ and every other stack empty reaches the label
$\mathit{yes}$ if $f(x, w)$ is true and $\mathit{no}$ otherwise within $p(|x| + |w|)$ steps. Then
for all bit lists $x$ and $w$, with $n$ the length of the pair encoding of $(x, w)$, the verifier
host program started at its first phase-0 label with state false, the pair encoding of $(x, w)$
on the input stack and every other stack empty halts within $T(n)$ steps, where $T$ is the
verifier host's step bound for $p$, with state false, the one-element list $[f(x, w)]$ on the
output stack and every other stack empty.
