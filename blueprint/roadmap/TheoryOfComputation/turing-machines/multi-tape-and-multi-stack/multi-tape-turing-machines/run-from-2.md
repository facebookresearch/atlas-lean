# Lockstep runs

Let $M$ and $M'$ be multi-tape Turing machines with the same number of
work tapes and the same alphabet, with state sets $Q$ and $Q'$, such that $M'$ simulates $M$ up
to the state relabelling $f : Q \to Q'$. For a configuration $c$ of $M$, write $f_*(c)$ for the
configuration of $M'$ obtained by replacing the state $q$ of $c$ by $f(q)$ and keeping the input
head, the work tapes, the work heads and the output (a halted configuration stays halted). Then
for every configuration $c$ of $M$ and every $t \in \mathbb{N}$, running $M'$ for $t$ steps from
$f_*(c)$ gives $f_*(c_t)$, where $c_t$ is the configuration reached by running $M$ for $t$ steps
from $c$.
