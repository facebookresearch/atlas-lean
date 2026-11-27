# Tseitin encoding of a Boolean circuit

Let $C$ be a De Morgan circuit with inputs $x_1,\dots,x_n$ and gates $w_1,\dots,w_s$ of fan-in at most two. The *Tseitin formula* $T(C)$ is the CNF over the variables $x_1,\dots,x_n,w_1,\dots,w_s$ containing, for each gate $w=\mathrm{op}(a,b)$, the at most four clauses of width at most three expressing $w\leftrightarrow \mathrm{op}(a,b)$, and the unit clause asserting the output. Then for every assignment $x$ to the inputs, $T(C)$ has a satisfying extension if and only if $C(x)=1$, and that extension is unique (it assigns each $w_j$ its value on $x$). Hence $C$ is satisfiable iff $T(C)$ is, and $|T(C)|=O(s)$.

## Proof sketch

The gate clauses force every gate variable to equal the value of its gate, by induction along the topological order; the output clause then asserts $C(x)=1$.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Tseitin CNF](../../../../../Logic/propositional-logic/tseitin-transformation/tseitin.md)
- [Satisfiability of a CNF formula](../../../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- G. S. Tseitin, "On the Complexity of Derivation in Propositional Calculus", Automation of Reasoning: 2: Classical Papers on Computational Logic 1967–1970, 1983.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
