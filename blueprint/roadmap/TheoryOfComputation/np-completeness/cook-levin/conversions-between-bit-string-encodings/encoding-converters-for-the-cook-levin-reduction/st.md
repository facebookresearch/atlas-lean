# States of the converter to the canonical pair encoding

A state of the converter is
either empty or one symbol of the verifier's input alphabet, that is, a left-tagged bit, a
right-tagged bit or the separator.

The state holds the last symbol popped; bits popped from the stashes are stored as left-tagged
bits.
