# The tokenizer embeds in the SAT verifier host

For every flag $c$, the tokenizer program
embeds in the host program with flag $c$ along the stack embedding of the tokenizer into the host
and the map of tokenizer labels into host labels, which sends the tokenizer's accepting label to
the start label of the clause-length filter, its rejecting label to the cleanup label with answer
false, and every other label $\ell$ to the host label running the tokenizer at $\ell$. That is,
for every tokenizer label $\ell$, either the tokenizer's statement at $\ell$ is the halt
statement, or the host program's statement at the image of $\ell$ is the tokenizer's statement
at $\ell$ translated along this embedding and label map.
