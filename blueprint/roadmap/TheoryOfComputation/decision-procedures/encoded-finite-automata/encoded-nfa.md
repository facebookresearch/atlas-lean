# Encoded NFA

An encoded NFA over an alphabet $\alpha$ is a nondeterministic finite
automaton with ε-moves given as data, with natural numbers as states: a list of start states, a
list of accepting states, a list of transitions $((s, a), t)$, meaning that on the letter $a$ the
state $s$ may move to $t$, and a list of ε-moves $(s, t)$, meaning that the state $s$ may move to
$t$ without reading a letter.
