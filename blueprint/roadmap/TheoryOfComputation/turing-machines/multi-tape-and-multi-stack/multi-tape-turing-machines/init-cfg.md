# Initial configurations under relabelling

Let $M$ and $M'$ be deterministic machines with
$k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling $f$.
Then for every input word $x$, the initial configuration of $M'$ on $x$ is the initial
configuration of $M$ on $x$ with its state $q$ replaced by $f(q)$.
