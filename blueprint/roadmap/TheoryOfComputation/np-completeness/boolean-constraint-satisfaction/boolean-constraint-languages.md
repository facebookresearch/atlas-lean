# Boolean constraint languages and polymorphisms

A Boolean **constraint language** $\Gamma$ is a finite set of relations $R\subseteq\{0,1\}^{r}$ of fixed arities. An instance of $\mathrm{CSP}(\Gamma)$ is a set of constraints $R(x_{i_1},\dots,x_{i_r})$ with $R\in\Gamma$; it is satisfiable if some assignment satisfies all of them. A function $f:\{0,1\}^{m}\to\{0,1\}$ is a **polymorphism** of $\Gamma$ if, for every $R\in\Gamma$, applying $f$ coordinatewise to any $m$ tuples of $R$ yields a tuple of $R$. The relevant polymorphisms are the constants $0$ and $1$, binary AND and OR, the ternary majority $\mathrm{maj}(a,b,c)$ and the ternary parity $a\oplus b\oplus c$.

## Depends on

- [The 3SAT decision problem](../satisfiability/3-satisfiability/sat3-dec.md)

## Sources

- Thomas J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th Annual ACM Symposium on Theory of Computing, 1978.
- Hubie Chen, "A Rendezvous of Logic, Complexity, and Algebra", arXiv:cs/0611018, 2006.
