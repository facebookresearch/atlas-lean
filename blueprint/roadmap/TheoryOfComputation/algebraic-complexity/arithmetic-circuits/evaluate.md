# Operand evaluation

Let $F$ and $A$ be types and $n \in \mathbb{N}$. Given a value in $F$
for each input $a \in A$ and a value in $F$ for each node $i < n$, an arithmetic operand over $F$
with inputs indexed by $A$ and $n$ nodes evaluates as follows: a constant $x$ evaluates to $x$, an
input $a$ to its assigned value, and a reference to node $i$ to the value given for node $i$.
