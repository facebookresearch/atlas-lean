# L-reductions

Write $\mathrm{opt}_M(x)$ for the optimum of an NPO problem $M$ on an
instance $x$ and $v_M(x, s)$ for the value of a solution $s$ for $x$. An NPO problem $M_1$
L-reduces to an NPO problem $M_2$ when there are polynomial-time computable maps $f$, from
bitstrings to bitstrings, and $g$, from pairs of bitstrings to bitstrings, and rational numbers
$\alpha > 0$ and $\beta > 0$, such that for every instance $x$ the following hold. First,
$\mathrm{opt}_{M_2}(f(x)) \le \alpha \, \mathrm{opt}_{M_1}(x)$. Second, for every solution $s$
that is feasible for $f(x)$ in $M_2$, the solution $g(x, s)$ is feasible for $x$ in $M_1$ and
$\mathrm{opt}_{M_1}(x) - v_{M_1}(x, g(x, s)) \le
\beta \, (\mathrm{opt}_{M_2}(f(x)) - v_{M_2}(f(x), s))$.

This is the L-reduction of Papadimitriou and Yannakakis, with polynomial-time maps $f$ and $g$.
