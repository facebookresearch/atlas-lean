# The accept generator as a finite multi-stack machine

For a layout $L$ with $g$ symbol
codes and natural numbers $n_1, a, k_1, e$, this is the finite multi-stack Turing machine whose
stacks are an output stack of bits and one unary counter for each of the generator's sixteen
counter names, whose input stack is the counter $T_n$ and output stack the bit stack, whose labels
are the generator's labels for $n_1$ code clauses and $g$ cell clauses with start label the first
precomputation stage, whose internal states are booleans with initial state false, and whose
transition function is the accept generator for $L$, $n_1$, $a$, $k_1$, $e$.

It serves only to check that the generator meets the finiteness conditions of a finite machine.
