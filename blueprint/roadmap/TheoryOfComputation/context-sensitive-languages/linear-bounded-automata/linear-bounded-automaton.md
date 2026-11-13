# Linear bounded automaton

A **linear bounded automaton**: a nondeterministic Turing machine whose
tape is the input word. The transition function gives, for a state, the
symbol under the head (`none` for a blank cell), and the boundary tag of
the head position, the finite set of possible next states, symbols to
write (`none` for a blank), and head moves. The boundary tag is what lets
the machine detect the ends of its tape: without it the model could not
recognize general context-sensitive languages. A move that would take
the head off the tape is not a step.
