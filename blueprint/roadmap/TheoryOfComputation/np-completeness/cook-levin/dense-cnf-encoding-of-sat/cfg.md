# Configurations of the dense-SAT verifier

A configuration of the verifier is a
configuration of the multi-stack Turing machine model with the verifier's labels, states and
stack alphabets. It consists of an optional current label (absent once the machine has halted),
a state, which is either a symbol of the work alphabet $G$ or nothing, and for each stack the
list of symbols on it: Booleans on the output stack and symbols of $G$ on each of the four work
stacks.
