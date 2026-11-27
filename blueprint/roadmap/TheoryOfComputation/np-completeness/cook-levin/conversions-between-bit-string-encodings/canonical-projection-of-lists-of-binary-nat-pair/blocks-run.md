# Pair-list projector main loop emits both lists in reverse

Let $p^1, \ldots, p^k$ be bit strings, $X = f(p^1) \cdots f(p^k)$ the concatenation of their framed forms, and
suppose the decoder of lists of pairs of natural numbers (see [projection length](projection-length-le.md)) returns
$((m_1, n_1), \ldots, (m_k, n_k))$ on $X$. Let $a_1$, $a_2$, $o_1$, $o_2$ be bit strings and $v$ a Boolean. Started
at label loop with internal state $v$, input $X$, accumulators $a_1, a_2$, outputs $o_1, o_2$ and empty workspace,
the [pair-list projector](prog.md) reaches label $\mathrm{finish}(\text{first})$ with internal state $0$ (false),
empty input, first accumulator the code of $(m_1, \ldots, m_k)$ reversed followed by $a_1$, second accumulator the
code of $(n_1, \ldots, n_k)$ reversed followed by $a_2$, outputs $o_1, o_2$ and empty workspace in at most
$12|X| + 1$ steps.
