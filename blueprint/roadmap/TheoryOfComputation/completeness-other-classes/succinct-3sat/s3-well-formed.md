# Well-formed succinct 3SAT descriptors

Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$ be a natural number. The descriptor $C$ is well-formed for
$n$ when $C$ has at least $n + 1$ gates, every gate of $C$ is valid for $n$, and the flat Boolean
circuit on $n + 2$ inputs obtained by decoding every gate of $C$ is well-formed.
