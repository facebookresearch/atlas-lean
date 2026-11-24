# Four-output decoder reaches exactly the canonical decoding outcome

Let $x$, $o_w$, $o_v$, $o_c$, $o_t$ be bit strings and $v$ a Boolean. There are an internal state $w$ and stack
contents $S$ such that the [four-output decoder](prog.md), started at label $\mathrm{split}(\mathrm{read})$ with
internal state $v$ and stacks $\mathrm{st}(\varepsilon, x, o_w, o_v, o_c, o_t)$, reaches in at most $9|x| + 2$
steps, with internal state $w$ and stacks $S$, the label good if the decoder of [run on success](run-some.md)
succeeds on $x$ and bad if it fails; moreover, if it returns $(((m_1, n_1), \ldots, (m_k, n_k)), (c, t))$, then $S$
is the final stack contents described in [run on success](run-some.md).
