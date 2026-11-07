# Encoding a dense clause block by block

Let $\ell = [(p_1, b_1), \dots, (p_n, b_n)]$ be
a list of literals with $p_1 < p_2 < \dots < p_n < V$. Then the bit encoding of the dense clause
over $V$ variables with literals $\ell$ is the gap encoding of $\ell$ from slot $0$ to $V$,
followed by the clause terminator $00$.
