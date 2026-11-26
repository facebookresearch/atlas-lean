# Bitstring encodings

A canonical bitstring encoding of a type $\alpha$ consists of an
encoding map from $\alpha$ to finite lists of booleans and a partial decoding map from finite
lists of booleans to $\alpha$, such that decoding the encoding of any $a \in \alpha$ succeeds
and returns $a$.

## Sources

- Encodings of a type by bitstrings, adapted from the Formal Conjectures project, https://github.com/google-deepmind/formal-conjectures.
