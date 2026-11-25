# Concatenation of ε-NFAs

Given ε-NFAs $M$ with state set $\sigma$ and $N$ with state set
$\tau$ over the same alphabet, their concatenation is the ε-NFA on the disjoint union
$\sigma \sqcup \tau$ whose moves are the moves of $M$, the moves of $N$, and an ε-move from every
accepting state of $M$ to every start state of $N$. Its start states are the start states of $M$
and its accepting states are the accepting states of $N$.
