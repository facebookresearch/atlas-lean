# Distributed transaction in UNSAFE LOCKING POLICY for two distributed transactions

In UNSAFE LOCKING POLICY for two distributed transactions, a distributed transaction is a pair: a list of steps, and a list of pairs $(p, q)$ of natural numbers, each read as "step $p$ precedes step $q$". The list of pairs is arbitrary data: only well-formedness of the transaction requires each pair to name two positions of the step list with $p < q$, and requires the pairs to form a transitively closed order relating every two steps on variables of the same site.
