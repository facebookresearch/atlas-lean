# Boolean combinations of polynomial-time deciders

For every fixed Boolean operation $\circ$ and polynomial-time computable functions $L_1, L_2$ from bit lists to Booleans, the function $x \mapsto L_1(x) \circ L_2(x)$, in which both deciders receive the same full input, is polynomial-time computable.

In terms of classes: if $L_1$ and $L_2$ are in P, so is the problem $x \mapsto L_1(x) \circ L_2(x)$, since membership in P is exactly being decided in polynomial time.
