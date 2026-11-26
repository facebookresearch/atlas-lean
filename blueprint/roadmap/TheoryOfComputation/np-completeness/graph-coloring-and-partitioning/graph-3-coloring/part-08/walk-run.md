# The joint walk of the 3-COLOR verifier decides one edge

Let $u, v$ be natural numbers,
$\mathit{pre}$ and $\mathit{post}$ lists of color codes (pairs of bits), $s$ a bit and $S$ an
assignment of a list of symbols to every stack. Suppose that $S$ holds $u$ unit symbols on the
counter $U$ and $v$ on the counter $V$, the bits of $\mathit{post}$ on the color stack $P$ (each
code $(a, b)$ contributing $a$ then $b$, the first code on top), and the bits of $\mathit{pre}$,
flattened the same way, in reverse order on the scratch stack $T$. Started at the label
$\mathsf{walk}$ with internal state $s$ and stacks $S$, the verifier reaches within at most
$\max(u, v) + 1$ steps, with some internal state and stacks $S'$, the label $\mathsf{back}$ if the
edge $(u, v)$ passes against the colors $\mathit{post}$ and the label $\mathsf{no}$ otherwise. The
edge passes when $u$ and $v$ are both less than the length of $\mathit{post}$ and either $u = v$
or the codes at positions $u$ and $v$ of $\mathit{post}$ differ. If it passes then, with
$m = \max(u, v) + 1$, the stacks $S'$ hold the bits of $\mathit{post}$ after its first $m$ codes
on $P$, the bits of $\mathit{pre}$ followed by those of the first $m$ codes of $\mathit{post}$,
flattened and in reverse order, on $T$, nothing on $U$ and $V$, and agree with $S$ on every other
stack.
