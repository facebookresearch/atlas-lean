# Invariants of Hopcroft's loop

Let $M$ be a DFA with transition function $\delta$. A list
$P$ of sets of states and a waiting list $W$ of pairs $(C, b)$ of a set of states $C$ and a letter
$b$ satisfy the invariants when: (i) $P$ is a partition of the states into nonempty blocks;
(ii) for every $(C, b)$ in $W$, $C$ is an entry of $P$; (iii) for every letter $b$ and all states
$p$, $q$ lying in a common entry of $P$, if for every $C$ with $(C, b)$ in $W$ the states
$\delta(p, b)$ and $\delta(q, b)$ are both in $C$ or both outside $C$, then $\delta(p, b)$ and
$\delta(q, b)$ lie in a common entry of $P$; (iv) any two states lying in a common entry of $P$
are both accepting or both rejecting; and (v) any two states from which $M$ accepts the same
language lie in a common entry of $P$.
