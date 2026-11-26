# One execution step of an Ianov scheme

In STRONG INEQUIVALENCE OF IANOV SCHEMES, one execution step of a scheme $S$ (a list of quadruples of natural numbers) under interpretations $f_r$ and $p_r$, on a configuration $(c, x)$, where $c$ is the $0$-based index of the current instruction $I_{c+1}$, looks only at the entry $S_c$:

- an entry with tag $0$, $(0, r, a, b)$, is executed as the assignment $x \leftarrow f_r(x)$ and moves to index $c + 1$, whatever the values of the unused fields $a$ and $b$;
- an entry with tag $1$, $(1, r, j, k)$, leaves $x$ unchanged and moves to index $j - 1$ if $p_r(x)$ holds and to index $k - 1$ otherwise, so to $I_j$ or $I_k$ when $j, k \ge 1$;
- every other configuration is fixed: an entry with tag $2$ or larger (the halt instruction $(2, 0, 0, 0)$, but also, for example, $(2, 1, 0, 0)$), and an index $c$ with no entry ($c$ at least the length of $S$).

A fixed configuration is therefore not necessarily a halt: see [halting](halts-with.md). Subtraction is natural-number subtraction, so $a - b = 0$ whenever $a \le b$.
