# Embedded SUBSET-SUM summing component reaches the mapped label

Let a host machine contain the [SUBSET-SUM verifier program](../part-05/prog.md): its stacks include images of the verifier's
stacks under an injective map, each with an alphabet identified with the verifier's, and at the
image $\varphi(\ell)$ of every verifier label $\ell$ under a label map $\varphi$ with
$\varphi(\mathsf{yes}) = \varphi(\mathsf{no})$, the host runs the verifier's instruction on the
image stacks, except at the verifier's halting labels. Let $a = (a_1, \dots, a_k)$ be a list of
natural numbers, $w$ a list of bits, $v$ a Boolean, $r$ the concatenation of the blocks of
$a_1, \dots, a_k$ (as on [SUBSET-SUM verifier computes the mask-selected sum](sum-component-run.md))
and $s$ the sum of the numbers chosen from $a$ by $w$. If the host's stacks $S$ hold $r$ on the
image of $X$, $w$ on the image of $W$ (as bit symbols) and nothing on the images of the other
verifier stacks, then from label $\varphi(\mathsf{next})$ with internal state $v$ the host reaches
label $\varphi(\mathsf{yes})$ in at most $|r|(2|r| + 6) + |r| + 3$ steps, with stacks $S'$ that
hold some list of bit symbols on the image of $W$, the binary code of $s$ in reverse order on the
image of $B$ and nothing on the images of the other verifier stacks, and that agree with $S$ on
every stack outside the images.
