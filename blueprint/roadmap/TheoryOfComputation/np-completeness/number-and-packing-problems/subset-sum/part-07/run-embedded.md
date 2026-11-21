# Embedded run of the binary addition component

Let a host machine contain the [binary addition machine](../part-06/prog.md): its stacks include
images of the verifier's seven stacks under an injective map, each with an alphabet identified
with the verifier's, and at the image $\varphi(\ell)$ of every label $\ell$ of the addition
machine under a label map $\varphi$, the host runs the addition machine's instruction on the image
stacks, except at the addition machine's halting label. Let $m$, $n$ be natural numbers, $v$ a
Boolean and $N$ the length of the [framed input](../part-06/pair-input.md) of $m$ and $n$. If the
host's stacks $S$ hold the framed input of $m$ and $n$ on the image of $X$ (as bit symbols) and
nothing on the images of the other six stacks, then from label $\varphi(0)$ with internal state
$v$ the host reaches label $\varphi(3)$ in at most $N(2N + 6) + 2N + 8$ steps, with stacks $S'$
that hold the binary code of $m + n$ on the image of $A$, nothing on the images of the other six
stacks, and agree with $S$ on every stack outside the images.
