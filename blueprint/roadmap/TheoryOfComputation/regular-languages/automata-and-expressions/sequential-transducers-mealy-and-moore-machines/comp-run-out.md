# Output of a composite sequential transducer

Let $S_1$ be a sequential transducer from
$I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. For a transducer $S$, a state
$q$ and a word $w$, write $\lambda_S(q, w)$ for the concatenation of the words $S$ emits while
reading $w$ from $q$ (without initial or final output). Then for all states $q_1$ of $S_1$ and
$q_2$ of $S_2$ and every word $x$ over $I$,
$\lambda_C((q_1, q_2), x) = \lambda_{S_2}(q_2, \lambda_{S_1}(q_1, x))$.
