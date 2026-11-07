# Splitting off the middle clause of a concatenation

Let $P$ and $Q$ be CNF formulas, $C$ a
clause, and $\varphi$ the formula whose clauses are those of $P$, then $C$, then those of $Q$.
Write $|P|$ for the number of clauses of $P$ and $\varphi_j$ for clause $j$ of $\varphi$, counting
from $0$ (the empty clause if $j$ is out of range). Let $f$ map each natural number $j$ and clause
to a list of elements of a type $\alpha$. Then concatenating the lists $f(j, \varphi_j)$ over
$j < |P| + 1$ in increasing order gives the concatenation of the lists $f(j, \varphi_j)$ over
$j < |P|$, followed by $f(|P|, C)$.
