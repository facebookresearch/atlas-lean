# Soundness of the tail of a chain

Let $C$ be a nonempty clause and $z$ a natural number. If
an assignment $v'$ satisfies every clause of $\mathrm{chainTail}(C, z)$ and gives the fresh
variable $\mathrm{fresh}(z)$ the value true, then the assignment $n \mapsto v'(2n)$ satisfies
$C$.
