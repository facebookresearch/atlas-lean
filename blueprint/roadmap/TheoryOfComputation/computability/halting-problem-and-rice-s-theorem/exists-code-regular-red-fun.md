# A single code for the regularity reduction function

For a pair $q = (c, n)$ of a partial
recursive code and a natural number, let $g_q$ be the partial function on $\mathbb{N}$ that on
input $x$ halts with output $0$ if $x$ is a perfect square, and otherwise runs $c$ on $n$ and,
if that halts, outputs $0$ (and is undefined if it does not). Write $\ulcorner q \urcorner$ for
the standard encoding of $q$ as a natural number, and $\langle a, b \rangle$ for the standard
pairing of natural numbers $a$ and $b$. There is a partial recursive code $U$ such that for every
such pair $q$ and every $x \in \mathbb{N}$, the value of $U$ at
$\langle \ulcorner q \urcorner, x \rangle$ equals $g_q(x)$ as a partial value: one is defined
exactly when the other is, and then they agree.
