# Serialized gates of five-worlds circuits

A serialized gate of a flat Boolean circuit is a
pair $(k, r)$ of a natural number $k$ (the gate kind) and a list $r$ of natural numbers (its
references, depending on the kind: an input index, a constant bit, or indices of other gates), in
the shared encoding of gates as (kind, references) pairs.
