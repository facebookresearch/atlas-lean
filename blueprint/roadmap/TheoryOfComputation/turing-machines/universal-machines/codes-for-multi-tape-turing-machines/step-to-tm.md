# Step of the machine of a code

For a code $c$, a binary input $x$ and a configuration $C$
of the machine of $c$ on $x$, the step of the machine of $c$ sends $C$ to its successor under
the transition function of $c$: $C$ itself if it has halted, and otherwise the result of
applying to $C$ the action that the transition function of $c$ selects for the state of $C$ and
the symbols under its heads.
