# Encoding a gate as a (kind, references) pair

A gate of a flat Boolean circuit on $n$
inputs is encoded as a pair of a natural number (its kind) and a list of natural numbers (its
references), the shared encoding used by decoding-based problems such as Circuit Value and
succinct circuits: the input variable $x_i$ is encoded as $(0, [i])$; the constant true as
$(1, [1])$ and the constant false as $(1, [0])$; the negation of gate $a$ as $(2, [a])$; the
conjunction of the gates listed in $r$ as $(3, r)$; and the disjunction of the gates listed in $r$
as $(4, r)$. Mod gates have no encoding of their own: every mod gate is encoded as $(5, [])$.

The serial evaluator reads kind $5$ as false.
