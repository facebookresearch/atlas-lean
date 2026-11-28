# Straight-line string constraints

A straight-line string constraint orders its relational atoms as single assignments $x_i = P_i$, each by concatenation or by a transducer, where every $P_i$ uses only input variables or earlier assigned ones, and adds a regular constraint; it models a loop-free string program in single static assignment form, with free inputs.

Use the relational and regular constraints of [string constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md), writing a transducer atom $R(x, y)$ as $y = R(x)$ and, following the source's convention, treating an equation $y = w$ with a constant word $w$ as the regular atom $y \in \{w\}$. An empty concatenation $y = x_1 \cdots x_n$ with $n = 0$ has the same solutions as $y = \varepsilon$ and is treated the same way, so every concatenation conjunct below has $n \ge 1$ (this normalization is ours; it preserves the set of solutions). A variable $x$ is a *source variable* of a relational constraint $\varphi$ if $\varphi$ has no conjunct $x = x_1 \cdots x_n$ and no conjunct $x = R(y)$.

A relational constraint $\varphi$ is *straight-line* if its conjuncts can be reordered as $\bigwedge_{i=1}^m x_i = P_i$, where each $P_i$ is a concatenation $y_1 \cdots y_n$ of variables or a transduction $R(y)$, such that

- (SL1) the variables $x_1, \dots, x_m$ are pairwise distinct, and
- (SL2) every variable occurring in $P_i$ is a source variable of $\varphi$ or one of $x_1, \dots, x_{i-1}$.

A *straight-line string constraint* is the conjunction of a straight-line relational constraint with a regular constraint (a Boolean combination of atoms $P(x)$). The class of all of them is denoted $\mathrm{SL}$. It is satisfied by an assignment to all its variables, source and assigned, that satisfies every conjunct. Because a transduction is a relation, a choice of input words may admit zero, one or several consistent valuations of the assigned variables; the constraint is satisfiable when, for some input words, at least one consistent valuation also satisfies the regular constraint.

The *dependency graph* of a relational constraint $\varphi$ is the directed graph on its variables with an edge from $x$ to $y$ when $\varphi$ has a conjunct $y = R(x)$, or a conjunct $y = x_1 \cdots x_n$ with $x$ among the $x_i$. A relational constraint is straight-line if and only if it is *uniquely definitional* (no two conjuncts have the same left-hand variable) and its dependency graph is acyclic.

## Depends on

- [String constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md)

## Proof depends on

None.

## Expansion

This is a definition. A straight-line ordering is a topological order of the dependency graph, so the graph is acyclic; conversely, for a uniquely definitional constraint with acyclic dependency graph, any topological order lists the defining conjuncts as required by (SL1) and (SL2). The source adds that recognizing straight-line constraints and producing such an ordering takes linear time, by checking unique definitionality with one bit per left-hand variable and then computing a topological sort, linear in the size of the constraint written with indexed variable occurrences. Straight-line constraints exclude the undecidable shapes $x = y \wedge R(x, y)$ and $x = y z \wedge R(z, x)$. Unlike [closed straight-line systems](../string-constraints-and-word-equations/the-closed-straight-line-fragment-is-decidable/slsys.md), in which every variable is defined by a deterministic term and satisfiability is decided by evaluation, source variables here are free inputs and transductions are relations.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Section 4, the Convention, the definition of source variables, Definition 4 (straight-line constraints), Proposition 4 and the paragraph after it (dependency graph, unique definitionality, linear-time recognition).
