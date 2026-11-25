# The MPCP instance of a reachability instance

Let $(R, x, y)$ be an instance of the
reachability problem over an alphabet $\alpha$, where $R = [(l_1, r_1), \dots, (l_k, r_k)]$, and
write $\#$ for the separator and $\diamond$ for the end marker of the extended alphabet
$\mathrm{Sym}(\alpha)$, in which letters of $\alpha$ are read as letters. Let $a_1 \cdots a_m$ be
the word $l_1 r_1 l_2 r_2 \cdots l_k r_k \, x \, y$, the letters of the instance. The MPCP
instance of $(R, x, y)$ is the list of dominoes (top word, bottom word)
$(\diamond, \diamond x \#), (y \# \diamond, \diamond), (\#, \#), (l_1, r_1), \dots, (l_k, r_k),
(a_1, a_1), \dots, (a_m, a_m)$, in this order. Its first domino is $(\diamond, \diamond x \#)$.
