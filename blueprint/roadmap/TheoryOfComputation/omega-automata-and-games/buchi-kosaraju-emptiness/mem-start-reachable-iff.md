# Mem start Reachable iff

Assume that `V` carries a Boolean equality test `==` that agrees with equality and a hash function and that `start` is a decidable predicate.

DFS preorder from the start states enumerates exactly the vertices
reachable from a start state (`mem_preorder_iff_reachable`, with the roots
being the filtered start vertices).
