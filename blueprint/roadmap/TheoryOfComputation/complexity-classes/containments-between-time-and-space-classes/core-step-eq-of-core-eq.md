# The next core depends only on the current core

For a multi-tape Turing machine with an output tape, if two configurations agree on their core (control state, input head position, and work tapes with their head positions, everything but the output tape), then their successor configurations also agree on their core. The transition never reads the output tape.
