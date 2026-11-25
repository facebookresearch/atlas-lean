# The Circuit Value Problem

The Circuit Value Problem is the decision problem that accepts
a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of such triples,
to a triple $(n, C, a)$ of a natural number $n$, a list $C$ of encoded gates and a list $a$ of
booleans such that the flat Boolean circuit on $n$ inputs obtained by decoding the gates of $C$
is well formed, $a$ has length $n$, and the evaluation of $C$ on $a$ is a nonempty list whose
last entry is true. It rejects every bitstring that does not decode.
