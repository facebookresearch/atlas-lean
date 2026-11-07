# MAXSNP problems

A MAXSNP problem, in the normal form of Papadimitriou and
Yannakakis, is an NPO problem $M$, with value function $v$ and solution length bound $b$,
together with natural numbers $k$ and $N$, a polynomial-time computable map $W$ sending each
instance $x$ to a list $W(x)$ of windows, each a pair $(w, j)$ of a list
$w = (w_1, \dots, w_m)$ of natural numbers (variable indices) and a natural number $j$ (a
pattern index), and a function $\mathrm{acc}$ assigning a truth value to each pair of a natural
number and a bitstring, such that the following hold. There is a polynomial $q$ with
natural-number coefficients such that $W(x)$ has at most $q(|x|)$ entries for every instance
$x$. Every window $(w, j)$ in $W(x)$ has $|w| \le k$ and $j < N$. A bitstring $s$ is a feasible
solution for $x$ exactly when $|s| \le b(|x|)$. For every feasible solution $s$ for $x$, the
value $v(x, s)$ is the number of entries $(w, j)$ of the list $W(x)$, counted with
multiplicity, for which $\mathrm{acc}(j, (s_{w_1}, \dots, s_{w_m}))$ is true, where $s_i$ is
the bit of $s$ at position $i$ (counting from $0$), read as false when $i \ge |s|$.

The windows depend only on the instance, never on the candidate solution: only the fixed
predicate $\mathrm{acc}$ inspects bits of the solution. The counting equation is required only
for feasible solutions, because padding a solution with false bits preserves the window count
while sufficiently long paddings are infeasible.
