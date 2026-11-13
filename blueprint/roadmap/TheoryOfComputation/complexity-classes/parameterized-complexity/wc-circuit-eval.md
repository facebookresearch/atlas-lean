# Gate values of an encoded circuit

Let $C = (g_0, \dots, g_{m-1})$ be a list of gates
encoded as (kind, references) pairs and let $a = (a_0, \dots, a_{n-1})$ be a list of booleans.
The gate values of $C$ under $a$ are the values $(v_0, \dots, v_{m-1})$ of the flat Boolean
circuit on $n$ inputs obtained by decoding each $g_j$ to a gate on $n$ inputs, evaluated at the
assignment that gives input $i$ the value $a_i$.

Decoding turns an input gate with index $i \ge n$ into the constant false, so such inputs read
as false.
