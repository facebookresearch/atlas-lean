# New splitters for a split block

Given a waiting list $W$ of pairs of a set of states and a
letter and sets $S$ and $D$ of states, write $D_1 = D \cap S$ and $D_2 = D \setminus S$. The new
waiting entries for $D$ consist, for each letter $b$ in the enumeration order of the alphabet,
of both $(D_1, b)$ and $(D_2, b)$ if $(D, b)$ is in $W$, and otherwise of the single entry
$(E, b)$, where $E$ is the smaller of $D_1$ and $D_2$ by cardinality ($D_1$ on a tie).
