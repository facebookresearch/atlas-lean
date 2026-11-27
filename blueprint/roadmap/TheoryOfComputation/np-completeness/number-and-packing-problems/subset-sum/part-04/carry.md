# Carry bit of a full adder

For bits $a$, $b$ and a carry-in $c$, the carry out of adding
$a$, $b$ and $c$ is $(a \wedge b) \vee (c \wedge (a \oplus b))$, which is true iff at least two of
$a$, $b$, $c$ are true.
