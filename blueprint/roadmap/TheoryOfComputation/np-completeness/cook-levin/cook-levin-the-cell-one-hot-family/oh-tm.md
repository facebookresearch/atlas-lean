# The one-hot generator as a finite multi-stack Turing machine

For a layout, the one-hot generator as a finite multi-stack Turing machine: its stacks are the output bit stack and
one unary counter for each [counter of the generator](ck.md), with these alphabets; its input stack is the time
counter $T_n$ and its output stack is the output stack; its labels are the [labels of the generator](gl.md), with
start label the first precomputation label (incrementing $T_n$); its internal state is a Boolean, initially false;
and its program is the [one-hot generator](prog.md).

The generator also reads the height bound from the height counter $H_s$, which is not the input stack of this
machine.
