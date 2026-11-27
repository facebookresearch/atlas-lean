# The fenced machine halts on no padding of a word iff the machine does not halt on it

Let
$M$ be a single-tape machine over a finite inhabited alphabet and $w$ a word over that alphabet.
The fenced machine of $M$ halts on none of the fenced inputs of $w$, with $i$ padding cells on the
left and $j$ on the right for $i, j \in \mathbb{N}$, if and only if $M$ does not halt on $w$.
