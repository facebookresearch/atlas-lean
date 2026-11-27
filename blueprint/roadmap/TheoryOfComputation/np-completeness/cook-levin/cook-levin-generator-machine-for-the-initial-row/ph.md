# Loop phases of the initial-row generator

The five phase loops of the generator for the
initial-row clauses, in the order the generator runs them (its input loop runs between the
certificate phase and the two stack phases): the tail phase (the row-$0$ cells of the stack $k_0$
holding the input, past the certificate block, are empty), the prefix phase (an empty cell in the
certificate block is followed by an empty cell), the certificate phase (each certificate cell is
empty or holds a certificate code), and two stack phases making every stack other than $k_0$
empty, first the stacks $k > k_0$, then the stacks $k < k_0$.
