# Evaluation of a flat Boolean circuit

For a circuit on $n$ inputs given as a list of
gates $g_0, \dots, g_{m-1}$ and an assignment $\alpha$ of booleans to the inputs, the list of
gate values is $(v_0, \dots, v_{m-1})$, where $v_j$ is computed from $v_0, \dots, v_{j-1}$, a
reference to a gate $a \ge j$ reading as false: an input gate $i$ has value $\alpha(i)$, a
constant gate has its constant, a negation gate on $a$ has value $\lnot v_a$, an and gate (or
gate) has the conjunction (disjunction) of the values it references, and a mod gate with
modulus $k$ is true if and only if $k \ne 0$ and the number of its references with value true,
counted with multiplicity, is divisible by $k$.
