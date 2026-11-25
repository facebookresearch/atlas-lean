# Pair-list projector always terminates at the decoding outcome

Let $x$ be a bit string and $v$ a Boolean. There are an internal state $w$ and stack contents $S$ such that the
[pair-list projector](prog.md), started at label loop with internal state $v$, input $x$ and all other stacks empty,
reaches in at most $16|x| + 3$ steps, with internal state $w$ and stacks $S$, the label good if the decoder of lists
of pairs of natural numbers (see [projection length](projection-length-le.md)) succeeds on $x$ and bad if it fails;
moreover, if it returns $((m_1, n_1), \ldots, (m_k, n_k))$, then in $S$ the first output holds the code of
$(m_1, \ldots, m_k)$, the second output the code of $(n_1, \ldots, n_k)$, and every other stack is empty.
