# Appending a flat gate to a straight-line circuit

Let $c$ be a straight-line circuit over the unbounded fan-in signature, on $n$ inputs, with $k$ outputs,
and let $g$ be a flat gate whose references are all less than $k$. Appending $g$ to $c$ gives a circuit
with $k + 1$ outputs, the first $k$ of them those of $c$. An input gate $x_i$ adds no gate: its new
output is the input wire $i$. Every other flat gate adds one gate of the same kind, which reads the
outputs of $c$ named by its references and becomes the new last output: a constant adds a constant
with the same value, a negation adds a negation, and an AND, OR or MOD gate adds an AND, OR or MOD
gate (with the same modulus) with one argument per reference, in order.
