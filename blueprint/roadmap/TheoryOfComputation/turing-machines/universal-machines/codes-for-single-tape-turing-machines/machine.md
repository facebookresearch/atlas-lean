# The machine of a single-tape code

The machine of a code $c$ is the single-tape Turing
machine with states and symbols in $\mathbb{N}$ that, in state $q$ reading symbol $a$, halts if
the table lookup of $c$ at state $q$ and symbol $a$ has no entry, and otherwise, if the entry is
$(q', s)$, enters state $q'$ and does the action coded by $s$: $0$ moves left, $1$ moves right
and $a' + 2$ writes $a'$.
