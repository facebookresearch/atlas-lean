# Growth of the waiting list in one round

Let $M$ be a DFA with transition function
$\delta$ over a finite alphabet $\Sigma$, let $P$ be a list of sets of states with no repeated
entries, let $W$ be a list of pairs of a set of states and a letter, let $C$ be a set of states
and $a$ a letter, and let $S = \{q : \delta(q, a) \in C\}$ be the preimage of $C$ under $a$. Then
the waiting list after the splitter $(C, a)$, computed from the blocks $P$ and the rest $W$ of the
waiting list, has length at most $|W| + |\Sigma| \cdot k$, where $k$ is the number of entries of
$P$ split by $S$, that is, meeting both $S$ and its complement.
