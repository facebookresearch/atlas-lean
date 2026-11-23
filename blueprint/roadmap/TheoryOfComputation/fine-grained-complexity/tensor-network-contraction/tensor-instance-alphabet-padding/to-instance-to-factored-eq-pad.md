# Factoring and unfactoring a tensor instance gives its padding

Let $R$ be a complete-graph tensor instance on a finite linearly ordered vertex set with labels in
$A$, let $\Lambda$ be a finite set of labels in $A$ and $d \in A$, let $D$ be a finite set of names
in a type $A'$ and $\delta : A' \to A$ a map sending every element of $D$ into $\Lambda$. Take the
half-edge presentation of $R$ built from $\Lambda$ and $d$, and convert it back to a complete-graph
instance using the names $D$ and the renaming $\delta$ on every pair. The result is the padding of
$R$ with default $d$, names $D$ and renaming $\delta$.
