# Start states of a right-hand side in a DFA

Let $D$ be an encoded DFA, $R$ a list of
natural numbers (the items found so far) and $q \in \mathbb{N}$. The start states of a right-hand
side $\beta$, a list of grammar symbols, for $q$ given $R$ are defined by recursion on $\beta$: for
the empty right-hand side they are the one-element list $[q]$, and for a symbol $X$ followed by
$\beta'$ they are the states of $D$, in order, at which $X$ fits given $R$ and the start states of
$\beta'$ for $q$ given $R$.
