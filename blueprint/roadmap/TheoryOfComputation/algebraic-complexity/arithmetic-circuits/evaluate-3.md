# Circuit evaluation

Let $F$ be a type with addition, subtraction and multiplication and
let $c$ be an arithmetic circuit over $F$ with inputs indexed by $A$ and outputs indexed by $B$.
Given a value in $F$ for each input $a \in A$, the value of $c$ at an output $b \in B$ is the value
of the output operand of $b$, where a constant $x$ has value $x$, an input has its assigned value
and a reference to gate $g_j$ has the value of $g_j$, each gate being evaluated from the values of
the gates before it.
