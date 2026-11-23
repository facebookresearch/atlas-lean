# The tokenize-then-emit machine as a host component

Given an emitter $E$ with finitely
many stacks, finite stack alphabets and finitely many labels, and a list of $E$'s stacks that
contains every stack exactly once, this is the reduction-host component whose stacks, alphabets,
labels and program are those of the tokenize-then-emit machine for $E$, with its stacks listed
as the SAT tokenizer's six stacks followed by the given list of $E$'s stacks.
