# The dense-to-binary machine

The multi-stack Turing machine whose stacks are indexed by
the stack names (input, stash, output, the counters $n$, $k$, $m$ and the scratch $t$), each
with the Booleans as alphabet. It reads its input from the input stack and leaves its output on
the output stack; its labels are the program labels, starting at the label that moves the input
onto the stash; its internal state is an optional Boolean, initially empty; and each label runs
the corresponding statement of the program.
