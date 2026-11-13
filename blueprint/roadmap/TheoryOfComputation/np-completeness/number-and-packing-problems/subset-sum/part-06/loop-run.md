# The summing loop of the SUBSET-SUM verifier

Let $N$ be a natural number and $t$ a list
of symbols. Write $\langle m \rangle$ for the canonical binary code of a natural number $m$, least
significant bit first, and put a bit list on a stack as the list of its name-bit symbols. Let $n$
and $s$ be natural numbers, $r$ and $w$ bit lists and $v$ a Boolean, with $|r| \le n$ and
$|\langle s \rangle| + |r| \le N$. Start the SUBSET-SUM verifier at the label $\mathsf{next}$
with internal state $v$, with $r$ on $X$, $w$ on $W$, $t$ on $T$, $\langle s \rangle$ on $A$,
and the stacks $B$, $P$ and $Q$ empty. Then for some internal state $v'$ and stack contents $S'$
it runs within $|r| \cdot (2N + 6) + 1$ steps to the configuration with internal state $v'$,
stacks $S'$ and label $\mathsf{fmove}$ if parsing the number blocks of $r$ with fuel $n$
succeeds, and label $\mathsf{no}$ if it fails. Moreover, if that parsing gives the list of
numbers $a$, and $\sigma$ is $s$ plus the sum of the numbers of $a$ chosen by the mask $w$, then
$|\langle \sigma \rangle| \le N$, and for some list of symbols $w'$ the stacks $S'$ hold nothing
on $X$, $w'$ on $W$, $t$ on $T$, $\langle \sigma \rangle$ on $A$, and nothing on $B$, $P$ and
$Q$.
