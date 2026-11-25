# The initial-row generator

Let $L$ be a layout with $g$ symbol codes, let $i_c$ and $k_0$
be natural numbers and let $y$ be a list of certificate codes. The generator assigns to each label
of the initial-row generator for $L$ and $y$ a machine statement with a Boolean flag on the stacks
of the counter machine with the generator's counters plus an input stack of codes below $g$, as
follows. At the read test label $\mathrm{rd}(i)$ for a code $i < g$, it is the read test for code
$i$ that goes on success to the clause-start label of the input clause with code $i$ and on
failure to the label after a failed read test for $i$. At every other label, it is the statement
of the counter part of the generator for $L$, $i_c$, $k_0$, $y$ at that label, translated along
the embedding of the counter stacks into the generator's stacks, with labels unchanged.
