# Run of a Mealy machine

The run of a Mealy machine $M$ from a state $q$ on an input
word $a_1 \cdots a_n$ is the pair $(q_n, o_1 \cdots o_n)$, where $q_0 = q$ and, for each
$1 \le i \le n$, $M$ moves from $q_{i-1}$ on $a_i$ to $q_i$ emitting the output letter $o_i$.
