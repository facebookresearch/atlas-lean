# The clocked evaluator

Given a code $c$, a list of bits $x$ and a clock $T \in \mathbb{N}$,
run the simulation of $c$ on $x$ for at most $T$ steps. If it halts within $T$ steps, the result
is the output of the halting configuration: the tape from the head rightwards, with trailing
blanks dropped. Otherwise there is no result.
