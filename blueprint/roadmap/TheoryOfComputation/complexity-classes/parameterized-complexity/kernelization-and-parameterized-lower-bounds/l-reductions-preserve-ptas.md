# L-reductions preserve approximation and PTAS

An **L-reduction** from an optimization problem $A$ to $B$ is a pair of polynomial-time maps $(f,g)$ and constants $\alpha,\beta>0$ such that $\mathrm{OPT}_B(f(x))\le\alpha\,\mathrm{OPT}_A(x)$ and, for every feasible solution $y$ of $f(x)$, $|\mathrm{OPT}_A(x)-\mathrm{val}_A(g(x,y))|\le\beta\,|\mathrm{OPT}_B(f(x))-\mathrm{val}_B(y)|$. If $B$ has a PTAS then so does $A$: a solution of $f(x)$ within relative error $\varepsilon/(\alpha\beta)$ is mapped by $g$ to one within relative error $\varepsilon$.

## Proof sketch

Combine the two inequalities: the absolute error on $A$ is at most $\beta$ times that on $B$, which is at most $\frac{\varepsilon}{\alpha\beta}\mathrm{OPT}_B\le\frac{\varepsilon}{\beta}\mathrm{OPT}_A$.

## Depends on

- [The class PTAS](../../time-and-space-complexity-classes/ptas.md)
- [NPO optimization problems](../../time-and-space-complexity-classes/is-npo.md)

## Sources

- Christos H. Papadimitriou and Mihalis Yannakakis, "Optimization, Approximation, and Complexity Classes", Journal of Computer and System Sciences 43(3), 1991, Proposition 2.
