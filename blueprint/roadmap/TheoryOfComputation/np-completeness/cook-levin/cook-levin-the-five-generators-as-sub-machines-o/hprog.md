# The host program

Given the five generator programs (update, situation definition, shift,
accept and init), the host program runs init, then update, then situation definition, then shift,
then accept. At each label of a generator other than its final label, the host executes that
generator's statement with the generator's stacks embedded into the host stacks (output onto the
shared output stack, counters onto the generator's own private counter block, and for init the
input stack onto the host's input-code stack) and its labels renamed into the host's copy of
them. At a generator's final label the host performs one chaining step: it resets the Boolean
state to false and jumps to the start label of the next generator, and after accept it jumps to
the final host label, where it halts.
