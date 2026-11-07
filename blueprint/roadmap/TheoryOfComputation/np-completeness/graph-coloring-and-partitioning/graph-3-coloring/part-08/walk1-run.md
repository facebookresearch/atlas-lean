# The walk towards the farther endpoint decides the edge

Let $k$ be a stack of the 3-COLOR
verifier other than the color stack $P$ and the scratch stack $T$, $(a, b)$ a pair of bits, and
$\ell$ a label whose statement is the step of the walk towards the farther endpoint on the
counter $k$, holding the color $(a, b)$ and continuing at $\ell$. Let $j$ be a natural number,
$\mathit{pre}$ and $\mathit{post}$ lists of color codes, $s$ a bit and $S$ an assignment of a list
of symbols to every stack. Suppose that $S$ holds $j$ unit symbols on $k$, the bits of
$\mathit{post}$ on $P$ (each code $(a', b')$ contributing $a'$ then $b'$, the first code on top),
and the bits of $\mathit{pre}$, flattened the same way, in reverse order on $T$. Started at $\ell$
with internal state $s$ and stacks $S$, the verifier reaches within at most $j + 1$ steps, with
some internal state and stacks $S'$, the label $\mathsf{back}$ if $j$ is less than the length of
$\mathit{post}$ and the code at position $j$ of $\mathit{post}$ differs from $(a, b)$, and the
label $\mathsf{no}$ otherwise. If $j$ is less than the length of $\mathit{post}$, the stacks $S'$
hold the bits of $\mathit{post}$ after its first $j + 1$ codes on $P$, the bits of $\mathit{pre}$
followed by those of the first $j + 1$ codes of $\mathit{post}$, flattened and in reverse order,
on $T$, nothing on $k$, and agree with $S$ on every other stack.
