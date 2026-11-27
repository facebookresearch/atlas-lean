# Pair-list projector fails on malformed input in linear time

Let $x$ be a bit string on which the decoder of lists of pairs of natural numbers (see [projection
length](projection-length-le.md)) fails (the input is not a concatenation of framed blocks, or some block does not
code a pair). Let $a_1$, $a_2$, $o_1$, $o_2$ be bit strings and $v$ a Boolean. Started at label loop with internal
state $v$, input $x$, accumulators $a_1, a_2$, outputs $o_1, o_2$ and empty workspace, the [pair-list
projector](prog.md) reaches label bad, with some internal state and some stack contents, in at most $12|x| + 2$
steps. The work stacks may then hold partial data.
