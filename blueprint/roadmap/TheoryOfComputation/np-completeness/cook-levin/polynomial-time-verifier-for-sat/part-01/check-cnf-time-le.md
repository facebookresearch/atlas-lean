# Cost bound for the witness formula check

Let $N$ be a list of natural numbers, $w$ a list
of booleans and $\varphi$ a CNF formula, and let $L$ be the sum of the lengths of the clauses of
$\varphi$ (its total number of literals). The cost of checking $\varphi$ against $N$ and $w$ is at
most $L \cdot (|N| + 1)$, where $|N|$ is the length of $N$.
