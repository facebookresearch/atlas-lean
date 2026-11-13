# Integer linear-programming feasibility in fixed dimension

For a natural number $d$, this
decision problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
decoding, to a pair $(A, b)$ such that $A$ is a list of rows, each a list of exactly $d$ integers,
$b$ is a list of integers with as many entries as $A$ has rows, and there is an integer vector
$y \in \mathbb{Z}^d$ with $\sum_{j < d} A_{rj} y_j \le b_r$ for every row index $r$. Each integer
entry is given as a pair $(n, s)$ of a natural number and a sign, standing for $n$ if $s$ is true
and $-n$ otherwise. Every other bitstring is rejected.
