# Fourier–Motzkin elimination

Let $Ax \le b$ be a system of linear inequalities over $\mathbb{Q}$ in variables $x_1, \dots, x_n$, and $j$ an index. Partition the inequalities into those with positive, negative and zero coefficient of $x_j$; scale the first two kinds to the forms $x_j \le u_k(x')$ and $\ell_m(x') \le x_j$, where $x'$ are the other variables. The system consisting of the inequalities not containing $x_j$ together with $\ell_m(x') \le u_k(x')$ for every pair $(k, m)$ has a rational solution in $x'$ if and only if $Ax \le b$ has a rational solution; its solutions are exactly the projections of the solutions of $Ax \le b$.

## Sources

- A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986
- M. Lavrov, "Lecture 20: Fourier–Motzkin elimination", Math 482 lecture notes, University of Illinois, 2020, Section 2, <https://misha.fish/archive/docs/482-spring-2020/lecture20.pdf>
- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016; the authors' course slides for Part V, "Fourier-Motzkin variable elimination", <https://www.decision-procedures.org/slides/linear-fourier_motzkin.pdf>
