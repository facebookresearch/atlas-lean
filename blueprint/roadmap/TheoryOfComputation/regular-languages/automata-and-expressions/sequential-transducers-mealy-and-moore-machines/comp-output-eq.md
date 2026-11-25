# Total output of a composite sequential transducer

Let $S_1$ be a sequential transducer
from $I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. For a sequential
transducer $S$ with start state $s$, initial output $\iota$ and final output map $\phi$, and a
word $x$, let $\delta_S(s, x)$ be the state $S$ reaches by reading $x$ from $s$ and
$\lambda_S(s, x)$ the concatenation of the words it emits along the way, and call the
concatenation $\iota \, \lambda_S(s, x) \, \phi(\delta_S(s, x))$ the whole output of $S$ on $x$
(acceptance plays no role). Then for every word $x$ over $I$, the whole output of $C$ on $x$
equals the whole output of $S_2$ on the whole output of $S_1$ on $x$.
