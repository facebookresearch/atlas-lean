# Decoding a gate from its (kind, references) pair

A pair $(k, r)$ of a natural number $k$
and a list $r$ of natural numbers decodes to a gate of a flat Boolean circuit on $n$ inputs as
follows: $(0, [i])$ decodes to the input variable $x_i$ when $i < n$ and to the constant false
when $i \ge n$; $(1, [b])$ decodes to the constant that is true if and only if $b = 1$; $(2, [a])$
decodes to the negation of gate $a$; $(3, r)$ decodes to the conjunction of the gates listed in
$r$; and $(4, r)$ decodes to the disjunction of the gates listed in $r$. Every other pair,
including every pair of kind $5$ (the encoding of a mod gate), decodes to the constant false.

These defaults match the serial evaluator, which reads an unknown kind, and an input variable
with no corresponding input, as false.
