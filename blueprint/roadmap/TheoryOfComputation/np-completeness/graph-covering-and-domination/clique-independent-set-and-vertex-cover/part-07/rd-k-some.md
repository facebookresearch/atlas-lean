# Reading the first unary number in the KG-map machine

Let $m$ be a mode, $k$ and $i$
natural numbers and $r$ a list of bits. Consider a configuration of the KG-map machine $M_m$ at
the label read $k$, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of the list of $k$ trues, a false and then $r$, top first, and
stack $A$ holds $i$ copies of the unit symbol. Then in exactly $k + 1$ steps $M_m$ reaches the
label read $n$ with $X$ holding $\mathrm{bit}(b)$ for the bits $b$ of $r$, $A$ holding $i + k$
copies of the unit symbol, and every stack other than $X$ and $A$ unchanged.
