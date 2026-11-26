# Verifier host, canonical form

Let $c$ be a component machine with distinct stacks $c_X$
and $c_W$ and labels $\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, where
$\mathit{yes} \ne \mathit{no}$ and the statements at $\mathit{yes}$ and $\mathit{no}$ are the
halting statement. Let $g_X$ and $g_W$ map bits to symbols of $c_X$ and $c_W$, let $f$ assign a
boolean $f(x, w)$ to all bit lists $x$ and $w$, and let $p$ be a polynomial with coefficients in
$\mathbb{N}$. Suppose that for all bit lists $x$ and $w$, the component started at
$\mathit{start}$ with internal state false, with $g_X$ applied to each bit of $x$ on $c_X$, $g_W$
applied to each bit of $w$ on $c_W$ and every other stack empty, reaches in at most
$p(|x| + |w|)$ steps the label $\mathit{yes}$ if $f(x, w)$ is true and the label $\mathit{no}$ if
it is false. Then the map $(x, w) \mapsto f(x, w)$ on pairs of bit lists is polynomial-time
computable for the canonical bitstring encodings.
