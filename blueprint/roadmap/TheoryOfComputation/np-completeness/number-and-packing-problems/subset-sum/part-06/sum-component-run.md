# SUBSET-SUM verifier computes the mask-selected sum

Let $a = (a_1, \dots, a_k)$ be a list of natural numbers, $w$ a list of bits and $v$ a Boolean.
Let $r$ be the concatenation of the blocks of $a_1, \dots, a_k$, where the block of a natural number $m$ is its binary digits, least significant first (none for $m = 0$), each digit $c$ written as the two bits true, $c$, followed by a final false, and let
$s$ be the sum of the [numbers chosen](../part-04/pick.md) from $a$ by the mask $w$. Started at
label $\mathsf{next}$ with internal state $v$, with $r$ on the stack $X$ and $w$ on the witness
stack $W$ (as bit symbols) and every other stack empty, the [SUBSET-SUM verifier program](../part-05/prog.md) reaches, in at most
$|r|(2|r| + 6) + |r| + 3$ steps, the label $\mathsf{yes}$ if $s = 0$ and $\mathsf{no}$ otherwise,
with some internal state, some list of bit symbols on $W$, the binary code of $s$ (least
significant bit first) in reverse order on the stack $B$, and every other stack empty.
