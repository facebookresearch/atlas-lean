# Binary-index translation of a dense formula

The translation of a dense CNF formula
$\varphi$ replaces each clause $c$ of $\varphi$, keeping their order, by its binary-index
translation with offset $0$: if $c$ has length $L$, each slot $j$ of $c$ holding a literal of
polarity $b$ becomes the literal of polarity $b$ on variable $2^{L - 1 - j} - 1$, and absent slots
are dropped.
