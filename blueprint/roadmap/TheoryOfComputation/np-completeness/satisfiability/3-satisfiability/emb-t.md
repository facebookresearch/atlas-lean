# Embedding the tokenizer's stacks into tokenize-then-emit

The stack embedding of the SAT
tokenizer into the tokenize-then-emit machine for an emitter $E$: the tokenizer's token stack $T$
goes to $E$'s token stack, with token symbols translated by $E$'s bijection from token symbols to
that stack's alphabet, and each other tokenizer stack goes to its own copy among the tokenizer
stacks of the combined machine, with symbols left unchanged.
