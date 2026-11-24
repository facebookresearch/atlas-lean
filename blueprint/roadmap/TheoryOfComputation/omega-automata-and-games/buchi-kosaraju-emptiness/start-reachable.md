# Start Reachable

Assume that `V` carries a Boolean equality test `==` that agrees with equality and a hash function and that `start` is a decidable predicate.

The vertices reachable from a start state, computed by *one* DFS from
the start states — not by a per-state reachability oracle and not by an
`O(n³)` closure. This is the visited set the emptiness scanner tests SCC
blocks against.
