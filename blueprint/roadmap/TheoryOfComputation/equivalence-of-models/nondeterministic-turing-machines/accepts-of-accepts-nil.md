# An NTM that accepts the empty word accepts every word

Let $m$ be a single-tape nondeterministic Turing machine (in the model of this topic, whose transitions
cannot test for a blank). If $m$ accepts the empty word, then $m$ accepts every word over
its tape alphabet.

This is the case of the empty word in the closure of acceptance under extension on the right,
which holds in this model because no transition can test for a blank cell.
