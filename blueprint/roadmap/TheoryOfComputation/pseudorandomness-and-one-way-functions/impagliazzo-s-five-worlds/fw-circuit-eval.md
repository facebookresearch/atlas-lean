# Evaluation of an encoded flat circuit

Let $C$ be a flat Boolean circuit given as a list
of gates, each encoded as a (kind, references) pair, and let $a = (a_0, \dots, a_{k-1})$ be a
list of booleans. The gate values of $C$ on $a$ are the gate values, in order, of the circuit on
$k$ inputs obtained by decoding each gate of $C$, evaluated on the assignment that sends input
$i$ to $a_i$.

Decoding turns an input variable $x_i$ with $i \ge k$ into the constant false.
