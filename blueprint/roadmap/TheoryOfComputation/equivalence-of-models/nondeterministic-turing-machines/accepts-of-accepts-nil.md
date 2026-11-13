# An NTM that accepts the empty word accepts every word

If a single-tape nondeterministic
Turing machine $m$ accepts the empty word, then $m$ accepts every word over its tape alphabet.

This is a special case of acceptance being closed under extension on the right, a defect of
CSLib's definition of these machines.
