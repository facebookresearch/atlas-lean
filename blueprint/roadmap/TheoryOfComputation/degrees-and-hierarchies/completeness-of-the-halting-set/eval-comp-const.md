# Composing a code with a constant code ignores the input

Let $c$ be a code of a partial
recursive function and let $n, m \in \mathbb{N}$. The code that first computes the constant
function with value $n$ and then applies $c$, evaluated at $m$, gives the same partial value as
$c$ evaluated at $n$: one is defined exactly when the other is, and then they are equal.
