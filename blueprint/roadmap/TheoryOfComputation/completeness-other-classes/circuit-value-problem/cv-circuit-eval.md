# Evaluation of an encoded Boolean circuit

Let $n$ be a number of inputs, let $C$ be a
list of gates, each encoded as a (kind, references) pair, and let $a = (a_0, a_1, \dots)$ be a
list of booleans. The evaluation of $C$ on $a$ is the list of values of all gates, in order, of
the flat Boolean circuit on $n$ inputs obtained by decoding each pair of $C$, under the
assignment that sends each input $i < n$ to $a_i$, or to false when $i$ is at least the length
of $a$.
