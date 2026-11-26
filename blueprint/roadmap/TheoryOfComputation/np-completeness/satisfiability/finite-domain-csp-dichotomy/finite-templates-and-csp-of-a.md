# Finite relational templates and the homomorphism problem CSP(A)

A **relational signature** $\tau$ is a finite set of relation symbols $R$, each with an arity $\operatorname{ar}(R)\ge 1$. A **finite $\tau$-structure** $\mathbb{A}=(A;(R^{\mathbb{A}})_{R\in\tau})$ consists of a finite nonempty domain $A$ and relations $R^{\mathbb{A}}\subseteq A^{\operatorname{ar}(R)}$. A **homomorphism** $h:\mathbb{X}\to\mathbb{A}$ between $\tau$-structures is a map $h:X\to A$ such that $(x_1,\dots,x_r)\in R^{\mathbb{X}}$ implies $(h(x_1),\dots,h(x_r))\in R^{\mathbb{A}}$ for every $R\in\tau$; we write $\mathbb{X}\to\mathbb{A}$ if one exists.

For a fixed finite structure $\mathbb{A}$ (the **template**), the **constraint satisfaction problem** $\mathrm{CSP}(\mathbb{A})$ is the decision problem: given a finite $\tau$-structure $\mathbb{X}$, decide whether $\mathbb{X}\to\mathbb{A}$. Equivalently, the input is a conjunction of atomic formulas $R(x_{i_1},\dots,x_{i_r})$ over variables, and the question is whether some assignment of values in $A$ satisfies all of them. Since a candidate homomorphism is a polynomial-size certificate, $\mathrm{CSP}(\mathbb{A})\in\mathsf{NP}$ for every finite $\mathbb{A}$. Graph $H$-colouring is $\mathrm{CSP}(\mathbb{H})$ for a single binary symmetric relation, and $k$-colouring is $\mathrm{CSP}(\mathbb{K}_k)$.

## Depends on

- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [GRAPH HOMOMORPHISM as a decision problem](../../graph-coloring-and-partitioning/graph-homomorphism/graph-homomorphism-dec.md)

## Sources

- Tomás Feder and Moshe Y. Vardi, "The Computational Structure of Monotone Monadic SNP and Constraint Satisfaction: A Study through Datalog and Group Theory", SIAM Journal on Computing 28(1) (1998).
- Andrei Bulatov, Peter Jeavons and Andrei Krokhin, "Classifying the Complexity of Constraints Using Finite Algebras", SIAM Journal on Computing 34(3) (2005).
