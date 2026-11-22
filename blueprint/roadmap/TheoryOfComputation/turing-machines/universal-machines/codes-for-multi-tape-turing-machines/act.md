# Action of a code at a key

For a code $c$ with $k$ work tapes, a state
$q \in \mathbb{N}$, a symbol $a$ under the input head and symbols $w = (w_i)_{i < k}$ under the
work heads (each symbol a bit or the blank), the action of $c$ at $(q, a, w)$ is the coded action
of the first table entry of $c$ whose key is $(q, a, w)$, or, if there is no such entry, the
halting action, which moves no head, writes and emits nothing, and has no next state.
