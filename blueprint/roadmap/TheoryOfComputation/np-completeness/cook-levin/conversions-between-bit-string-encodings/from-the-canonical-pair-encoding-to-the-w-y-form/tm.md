# The pair-encoding converter machine

The converter is the finite multi-stack Turing
machine whose stacks are the input stack, the output stack and the two stash stacks, with bits
as the alphabet of every stack except the output stack, which holds the verifier's symbols. Its
labels are the five phases (read the first component, read the second, emit the second, emit
the separator, emit the first), and it starts in the phase that reads the first component. Its
internal state is an optional bit (the last bit popped), initially empty, and it runs the
converter program. Input is read from the input stack, which holds bits, and output is written
to the output stack.
