# Predecessors of a gate

For a gate $g$ of a flat Boolean circuit on $n$ inputs, this is
the list of gate indices that $g$ reads: the empty list for an input variable or a constant, the
one-element list $[a]$ for the negation of gate $a$, and the argument list $l$ for an and, or or
mod gate with argument list $l$ (the modulus of a mod gate is not included).
