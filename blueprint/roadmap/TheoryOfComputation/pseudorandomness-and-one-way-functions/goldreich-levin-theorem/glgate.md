# Serialized circuit gates

A serialized gate is a pair $(k, r)$ of a natural number $k$, the
kind of the gate, and a list $r$ of natural numbers, its references.

These pairs are read through the shared (kind, references) encoding of gates of flat Boolean
circuits.
