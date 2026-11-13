# The host as a finite multi-stack Turing machine

Given the five generator programs (update
and situation-definition programs over the family generator's stacks, a shift program, an accept
program, and an init program whose input alphabet has $g$ codes), the host machine is the finite
multi-stack Turing machine whose stacks are the host stacks, with the input-code stack as input
stack and the shared output stack as output stack, whose alphabets are the host alphabets, whose
labels are the host labels, whose start label is the init generator's start label, whose
internal state is a Boolean with initial value false, and whose program is the host program built
from the five generator programs.

This is a finiteness check only: the input and output stacks are provisional until the
precomputation is attached.
