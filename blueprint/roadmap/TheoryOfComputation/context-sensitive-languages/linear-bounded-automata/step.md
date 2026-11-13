# One step of a linear bounded automaton

One step of the machine: choose a transition for the current state,
the symbol under the head, and its boundary tag, write the symbol, move
the head legally. A step from a configuration whose head is off the
tape is impossible: legality requires the source head to be on the
tape.
