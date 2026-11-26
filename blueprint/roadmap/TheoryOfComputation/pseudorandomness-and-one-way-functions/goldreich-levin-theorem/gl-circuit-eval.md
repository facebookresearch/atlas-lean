# Gate values of a serialized circuit

For a list $C = (g_0, \dots, g_{m-1})$ of serialized
gates and a list $a = (a_0, \dots, a_{n-1})$ of Booleans, the gate values of $C$ on $a$ are the
list of gate values of the flat Boolean circuit on $n$ inputs whose $j$-th gate is decoded from the
(kind, references) pair $g_j$, evaluated on the assignment that gives input $i$ the value $a_i$.

A pair $(0, [i])$ with $i \ge n$ decodes to the constant false, so an input index out of range
reads as false.
