# Succinct 3SAT

Succinct 3SAT is the decision problem that accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, C)$ of a natural
number $n$ and a list $C$ of gates encoded as (kind, references) pairs such that $C$ is a
well-formed descriptor for $n$ and some assignment $\sigma$ of booleans to the natural numbers
satisfies clause $c$ of the formula described by $C$ for every $c < 2^n$. Bitstrings that do not
decode are rejected.
