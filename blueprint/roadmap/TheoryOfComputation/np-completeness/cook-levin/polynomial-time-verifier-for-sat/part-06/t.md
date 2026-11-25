# Tokenizer labels in the host machine

The map from labels of the tokenizer to labels of
the host SAT verifier sends the tokenizer's accepting label to the start label of the embedded
clause-length filter, its rejecting label to the cleanup label with answer false, and every
other label $l$ to the host label that runs the tokenizer at $l$.
