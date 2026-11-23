# Hamiltonian-cycle verifier

Given bit strings $x$ and $y$, let
$m = \lfloor \sqrt{|x|} \rfloor$ and let $w$ be the least natural number with $m \le 2^w$. The
verifier reads $x$ as the adjacency matrix of a graph on the vertices $0, \dots, m - 1$, stored
row by row, and $y$ as $m$ words of $w$ bits, the $i$-th word giving a number $v_i$ in binary,
least significant bit first. It accepts exactly when $|x| = m^2$, every diagonal entry of the
matrix is false, the matrix is symmetric, $m \ge 3$, $|y| = mw$, the numbers
$v_0, \dots, v_{m-1}$ are distinct and less than $m$, and $v_i$ is adjacent to
$v_{(i+1) \bmod m}$ for every $i < m$. Along with the answer it returns a step count of the
operations it performs: bit reads from $x$ and $y$, checks and updates.
