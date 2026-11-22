# The frame of a read

Let $d$ be a stack of the marking machine, $ps$ a list of pairs of a
stack and a symbol, $i$ a natural number, and $S$, $S'$ two contents of the stacks. Suppose every
stack $q$ other than the input $X$ and $d$ holds in $S'$ the list it holds in $S$ with $i$ further
copies of the symbol of the first entry for $q$ in $ps$ pushed on top (and unchanged if $ps$ has
no entry for $q$). Then $S'$ agrees with $S$ on every stack other than $X$, $d$ and the stacks
that have an entry in $ps$.
