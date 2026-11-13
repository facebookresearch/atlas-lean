# The cell-shift generator as a finite stack machine

For a layout $L$, situation tables
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations, the cell-shift
generator for these data, bundled as a multi-stack Turing machine with finitely many stacks,
labels and states: its stacks are the Boolean output stack and one counter stack for each counter
of the generator, its input stack is the counter $\mathrm{Tn}$ and its output stack is the Boolean
output stack, its alphabets are the counter-machine alphabets (Booleans on the output stack, a
unit symbol on each counter), its labels are the labels of the shift generator for $L$ and $N$,
execution starts at the first precomputation stage, its internal state is a Boolean, initially
false, and its transition function is the cell-shift generator.

It serves only to check that the generator meets the finiteness conditions of a finite machine.
