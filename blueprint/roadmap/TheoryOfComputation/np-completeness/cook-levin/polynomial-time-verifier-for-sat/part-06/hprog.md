# Program of the SAT verifier host

For a value $c$ of the 3SAT flag, the host program
acts at each host label as follows. Here moving a bit block from one stack to another means
repeatedly popping the top symbol of the first stack while it is a bit and pushing it, as a bit
token, onto the second, and continuing at the next label once the top is not a bit or the stack
is empty.

The phase-0 labels move the formula bits from the input stack onto a scratch stack, move them
from there onto the formula stack, pop one symbol (on a pair encoding, the separator) from the
input stack, move the certificate bits from the input stack onto a second scratch stack, and move
them from there onto the certificate stack before going to the start label of the tokenizer. At
a tokenizer label, a filter label or a driver label the host runs the program of the tokenizer,
of the 3-clause filter with flag $c$, or of the clause-check driver with its embedded lookup, on
that component's stacks embedded in the host, with the component's labels renamed to host
labels; the tokenizer's accept exit goes to the filter's start label, the filter's pass exit to
the driver's start label, the driver's yes exit to the cleanup label with answer true, and the
tokenizer's reject exit, the filter's fail exit and the driver's no exit to the cleanup label
with answer false. At the cleanup label with answer $b$ the host pops every stack other than the
output stack once, repeats this while anything was popped, and then goes to the output label
with answer $b$, where it pushes $b$ onto the output stack, sets its internal state to false and
halts.
