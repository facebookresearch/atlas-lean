# Cell-by-cell check of a code stack

The check of a bit list $x$ from a key $(p_q, p_a)$
of natural numbers is defined as follows. The empty list passes. Otherwise, calling the cell of a
number $n$ the $n$ bits $\mathrm{true}$ followed by one bit $\mathrm{false}$, read four cells off
the front of $x$, those of $q$, $a$, $q'$ and $s$ in this order, leaving the rest $r$. The check
fails if one of these cells cannot be read because what remains contains no bit
$\mathrm{false}$, or if the key $(q, a)$ is lexicographically below $(p_q, p_a)$, that is,
unless $p_q < q$, or $p_q = q$ and $p_a \le a$. Otherwise its result is the check of $r$ from
the key $(q, a + 1)$.

The reformatting machine checks its input this way.
