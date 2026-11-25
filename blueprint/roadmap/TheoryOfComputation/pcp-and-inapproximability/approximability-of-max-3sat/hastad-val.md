# Value of a MAX-3SAT assignment

For bitstrings $x$ and $a$, read $a$ as the assignment
giving variable $v$ the value $a_v$ if $v < |a|$ and false otherwise. If $x$ decodes, under the
canonical bitstring decoding, to a pair $(u, \varphi)$ of a bitstring $u$ and a CNF formula
$\varphi$ in which every variable index is less than $|u|$ and every clause is nondegenerate,
then the MAX-3SAT value of $a$ on $x$ is the number of clauses of $\varphi$, counted with
multiplicity, that contain a literal $(v, s)$ whose variable gets the value $s$. Otherwise the
value is $0$.

The bitstring $u$ gives the number of variables in unary. Since degenerate and malformed
instances get value $0$, the $7/8$ random-assignment bound holds on every instance with nonzero
value.
