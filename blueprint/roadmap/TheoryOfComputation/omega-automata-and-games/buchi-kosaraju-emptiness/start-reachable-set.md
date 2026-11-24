# Start Reachable Set

Assume that `V` carries a Boolean equality test `==` that agrees with equality and that `start` is a decidable predicate.

The start-reachable visited set as a hash set: one construction, then
one `contains` test per scanned state.
