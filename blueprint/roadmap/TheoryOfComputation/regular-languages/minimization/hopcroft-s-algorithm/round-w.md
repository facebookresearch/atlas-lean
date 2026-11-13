# One update of the waiting list

For a DFA $M$ with transition function $\delta$, a list $P$
of blocks of states, a list $W$ of pairs of a set of states and a letter, a set $C$ of states and a
letter $a$, let $S = \{q : \delta(q, a) \in C\}$ be the preimage of $C$ under $a$, and say that $S$
splits a set $D$ when $D$ meets both $S$ and its complement. The waiting list after the splitter
$(C, a)$, from the rest $W$ of the waiting list, consists of the entries of $W$ whose set is not
split by $S$, followed, for each block $D$ of $P$ split by $S$ in order, by the new splitters for
$D$: for each letter $b$ in the enumeration order of the alphabet, both $(D \cap S, b)$ and
$(D \setminus S, b)$ if $(D, b)$ is in $W$, and otherwise the single entry $(E, b)$, where $E$ is
the smaller of $D \cap S$ and $D \setminus S$ by cardinality ($D \cap S$ on a tie).
