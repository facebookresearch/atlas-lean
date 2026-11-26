# Clause loop of the clause check

Suppose the lookup sub-program $lk$ with start label
$l_0$ meets the lookup contract with constants $a$ and $b$. Let $es$ be a table with table stack
$B_{es}$, and let $\varphi$ be a CNF formula with clauses $D_1, \dots, D_m$. The stack tokens
of a clause are its clause marker followed by the stack tokens of its literals, last literal
first, where the stack tokens of a literal $(n, p)$ are the literal marker of polarity $p$
followed by the bits of the binary encoding of $n$ (least significant bit first, empty for
$n = 0$) in reverse order. Let $N$ be the total length of the stack tokens of
$D_1, \dots, D_m$. Start the clause-check machine with lookup $lk$ at label start, with any
internal state and with the stack tokens of $D_1$, then of $D_2$, up to $D_m$ on the token
stack $T$, $B_{es}$ on $B$, and $S$, $A$, $C$, $V$, $P$, $F$ empty. Then within
$N \cdot (a \cdot |B_{es}| + b + 5) + 1$ steps it reaches, with some internal state and some
stack contents, label yes if every clause $D_j$ has a literal $(n, p)$ such that the live value
of the binary encoding of $n$ in $es$ is $p$, and label no otherwise.
