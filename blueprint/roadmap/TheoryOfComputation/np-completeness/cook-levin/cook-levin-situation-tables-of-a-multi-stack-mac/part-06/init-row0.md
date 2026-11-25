# Init semantics

Fix an encoding $E$ of a machine $M$, lists $x$ and $Y$ of symbols of the
input alphabet, natural numbers $m$, $T$, $H$ with $|x| \le m < H$, and an assignment $a$ that
satisfies the init family of $E$ for $x$, $Y$, $m$, $T$ and $H$. Then there is a list $y$ of
input symbols, each occurring in $Y$, such that the concatenation $xy$ has length at most $m$ and
the row-0 obligation holds for $a$, height $H$ and the input $xy$.
