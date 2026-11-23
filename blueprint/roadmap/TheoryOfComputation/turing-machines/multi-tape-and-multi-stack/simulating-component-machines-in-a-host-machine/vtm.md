# The verifier host machine

The verifier host as a finite multi-stack Turing machine for a
component machine $c$: its stacks are the host stacks, with the pair alphabet on the input stack,
the alphabets of $c$ on the component's stacks and bits on the other stacks; its labels are the
host labels and its program is the verifier host program; it starts at the first phase-0 label
with a boolean internal state, initially false; it reads its input from the input stack and leaves
its output on the output stack.
