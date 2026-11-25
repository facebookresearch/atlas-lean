# The fenced machine halts on some padding of a word iff the machine halts on it

Let $M$ be
a single-tape machine over a finite inhabited alphabet and $w$ a word over that alphabet. The
fenced machine of $M$ halts on the fenced input of $w$ with $i$ padding cells on the left and $j$
on the right for some $i, j \in \mathbb{N}$ if and only if $M$ halts on $w$.

A halting run of $M$ of $n$ steps stays within $n$ cells of its start, so it runs unchanged inside
the walls of the fenced input of $w$ with $n + 1$ padding cells on each side; conversely, the
fenced machine halts only by simulating a halting run of $M$.
