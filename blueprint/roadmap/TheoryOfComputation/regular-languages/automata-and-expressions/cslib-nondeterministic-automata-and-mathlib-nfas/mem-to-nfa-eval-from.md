# Mem toεNFA eval From

Running the Mathlib form of a CSLib automaton from a set of states `S` on a word `xs`
reaches exactly the states that a CSLib saturated multistep transition labelled
`xs.map some` reaches from a state of `S`.
