# Reading the second unary number in the KG-map machine

Let $m$ be a mode, $n$ and $i$
natural numbers and $r$ a list of bits. Consider a configuration of the KG-map machine $M_m$ at
the label read $n$, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of the list of $n$ trues, a false and then $r$, top first, and
stacks $B$ and $D$ each hold $i$ copies of the unit symbol. Then in exactly $n + 1$ steps $M_m$
reaches the label move with $X$ holding $\mathrm{bit}(b)$ for the bits $b$ of $r$, $B$ and $D$
each holding $i + n$ copies of the unit symbol, and every stack other than $X$, $B$ and $D$
unchanged.
