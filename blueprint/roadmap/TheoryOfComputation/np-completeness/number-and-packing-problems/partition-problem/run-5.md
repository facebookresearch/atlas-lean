# Canonical PARTITION membership transducer runs in quadratic time

For every list $a = (a_1, \dots, a_n)$ of natural numbers, let $r$ be the concatenation of the
blocks of $a_1, \dots, a_n$, where the block of a natural number $m$ is its binary digits, least significant first (none for $m = 0$), each digit $c$ written as the two bits true, $c$, followed by a final false. The [membership transducer](prog-5.md)
started at $\mathsf{copy}$ with internal state false, with $r$ on $X$ and every other stack empty,
reaches $\mathsf{done}$ in at most $|r|(2|r| + 14) + 9$ steps, with some internal state and stack
contents in which the doubling machine's output stack $O$ holds the encoding of the SUBSET-SUM
instance with numbers $2a_1, \dots, 2a_n$ and target $a_1 + \dots + a_n$.
