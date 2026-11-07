# Unterminated first unary number in the KG-map machine

Let $m$ be a mode and $r$ a list
of bits on which reading a unary length prefix fails (this happens exactly when $r$ contains no
false). From any configuration of the KG-map machine $M_m$ at the label read $k$, with any
internal bit, in which stack $X$ holds the input symbols $\mathrm{bit}(b)$ for the bits $b$ of
$r$, top first, $M_m$ reaches the failure label in exactly $|r| + 1$ steps, with every stack
other than $X$ and $A$ unchanged.
