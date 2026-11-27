# Pair-list projector yields canonical weight and value lists

Let $x$ be a bit string on which the decoder of lists of pairs of natural numbers (see [projection
length](projection-length-le.md)) returns $((m_1, n_1), \ldots, (m_k, n_k))$, let $o_1$, $o_2$ be bit strings and
$v$ a Boolean. There is an internal state $w$ such that the [pair-list projector](prog.md) goes from label loop,
internal state $v$, input $x$, empty accumulators, outputs $o_1, o_2$ and empty workspace to label good, internal
state $w$, first output the code of $(m_1, \ldots, m_k)$ followed by $o_1$, second output the code of
$(n_1, \ldots, n_k)$ followed by $o_2$, and all other stacks empty, in at most $16|x| + 3$ steps.
