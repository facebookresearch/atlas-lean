# Four-output decoder fails on malformed input

Let $x$ be a bit string on which the decoder of [run on success](run-some.md) fails, let $o_w$, $o_v$, $o_c$, $o_t$
be bit strings and $v$ a Boolean. Started at label $\mathrm{split}(\mathrm{read})$ with internal state $v$ and
stacks $\mathrm{st}(\varepsilon, x, o_w, o_v, o_c, o_t)$, the [four-output decoder](prog.md) reaches label bad, with
some internal state and some stack contents, in at most $9|x| + 2$ steps. The work stacks may then hold partial
data.
