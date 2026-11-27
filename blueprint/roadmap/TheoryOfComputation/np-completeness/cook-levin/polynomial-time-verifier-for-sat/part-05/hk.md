# Stacks of the SAT verifier host

The SAT verifier host has seventeen stacks: the input
stack, the output stack, and fifteen work stacks, namely two holding the formula bits and the
certificate bits, two scratch stacks used to move them in phase 0, the token and table stacks,
six further stacks of the clause-check driver, two further stacks of the tokenizer, and one
further stack of the 3-clause filter.
