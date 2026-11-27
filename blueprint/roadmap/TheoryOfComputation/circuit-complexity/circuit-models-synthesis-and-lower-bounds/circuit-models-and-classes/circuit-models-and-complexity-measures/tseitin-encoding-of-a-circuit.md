# Tseitin encoding of a Boolean circuit

Let $C$ be a De Morgan circuit with inputs $x_1,\dots,x_n$, gates $w_1,\dots,w_s$ of fan-in at most two, and one output gate. The *Tseitin formula* $T(C)$ is the CNF with one variable for every node of $C$ (the inputs $x_1,\dots,x_n$ and the gate variables $w_1,\dots,w_s$) containing, for each gate $w=\mathrm{op}(a,b)$ (or $w=\neg a$), clauses of width at most three equivalent to the condition $w\leftrightarrow \mathrm{op}(a,b)$ (respectively $w\leftrightarrow\neg a$), and the unit clause asserting the output variable. Then $T(C)$ is satisfiable if and only if $C$ is satisfiable, and $T(C)$ has $O(s)$ clauses.

## Proof sketch

For an AND gate $w=a\wedge b$ the clauses are $(\neg w\vee a)$, $(\neg w\vee b)$ and $(w\vee\neg a\vee\neg b)$ (Arora and Barak list four clauses of width three); OR gates are dual, and a NOT gate $w=\neg a$ contributes $(w\vee a)\wedge(\neg w\vee\neg a)$. So there are at most $4s+1$ clauses. Derived here, by induction along a topological order: on every assignment satisfying the gate clauses each gate variable equals the value of its gate on the input part $x$; hence for each input $x$ the formula $T(C)$ has a satisfying extension of $x$ if and only if $C(x)=1$, and that extension is unique.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Tseitin CNF](../../../../../Logic/propositional-logic/tseitin-transformation/tseitin.md)
- [Satisfiability of a CNF formula](../../../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- G. S. Tseitin, "On the Complexity of Derivation in Propositional Calculus", Automation of Reasoning: 2: Classical Papers on Computational Logic 1967–1970, 1983.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007 (Section 6.7, Lemma 6.32 and its proof, p. 6.12).
