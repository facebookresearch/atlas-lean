# The init generator as a finite multi-stack machine

For a layout $L$ with $g$ symbol
codes, a start code $i_c$, a stack $k_0$ and a code list $Y$, this is the finite multi-stack
Turing machine whose stacks are the generator's counters, its Boolean output stack and an extra
input stack, with the extra stack as input stack and the Boolean stack as output stack; whose
stack alphabets are unit symbols on the counters, bits on the output stack and codes below $g$
on the input stack; whose labels are the generator's labels, starting at the first
precomputation label; whose internal state is a Boolean starting at false; and whose transition
function is the generator for $L, i_c, k_0, Y$.

It records only that the generator is a finite machine.
