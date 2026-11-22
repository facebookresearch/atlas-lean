# Outputs of an encoded circuit

Let $C$ be a list of $m$ gates encoded as
(kind, references) pairs, let $\alpha$ be a list of booleans and let $k$ and $n$ be natural
numbers. The last $k$ outputs of $C$ on $\alpha$ are the last $k$ of the gate values
$(v_0, \dots, v_{m-1})$ of $C$ on $\alpha$ as a circuit on $n + 2$ inputs, that is
$(v_{m-k}, \dots, v_{m-1})$; when $k > m$ they are all $m$ gate values.
