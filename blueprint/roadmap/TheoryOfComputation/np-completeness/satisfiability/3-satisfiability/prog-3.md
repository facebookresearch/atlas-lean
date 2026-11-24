# Program of the tokenize-then-emit machine

For an emitter $E$, the combined machine acts as
follows. At a label of the SAT tokenizer it runs the tokenizer's statement for that label, with the
tokenizer's token stack replaced by the token stack of $E$ (token symbols identified with those of
$E$), its other stacks kept as copies, and its labels renamed: acceptance goes to the start label
of $E$, rejection goes to the step that writes the undecodable-input output, and every other label
goes to its own copy. At a label of $E$ it runs the statement of $E$ on the stacks of $E$, with the
exit label of $E$ renamed to the exit label of the combined machine and every other label of $E$
kept. At the label for undecodable input it pushes, in one step, the fixed output that $E$ assigns
to undecodable input, as output symbols of $E$, onto the output stack of $E$ (so that the stack
then reads that output from the top) and goes to the exit label. At the exit label the machine
halts.
