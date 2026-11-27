# Factoring round trip with the full source alphabet

Let $R$ be a complete-graph tensor instance on a finite linearly ordered vertex set with labels in
a finite type $A$, let $d \in A$, let $D$ be a finite set of names in a type $A'$ and
$\delta : A' \to A$ any map. Take the half-edge presentation of $R$ built from all of $A$ and $d$,
and convert it back to a complete-graph instance using the names $D$ and the renaming $\delta$ on
every pair. The result is the padding of $R$ with default $d$, names $D$ and renaming $\delta$.
