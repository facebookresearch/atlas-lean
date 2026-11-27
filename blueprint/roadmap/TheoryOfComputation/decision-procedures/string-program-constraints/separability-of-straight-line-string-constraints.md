# Separability of straight-line string constraints

Whether the solution sets of two straight-line string constraints can be separated by a regular relation is undecidable, but separation by piecewise testable relations, which only look at scattered subwords, is decidable; separators act as interpolants for string constraints.

Let $\Sigma$ be a finite alphabet and $x_1, \dots, x_n$ string variables. An atomic constraint is a membership $x \in L(A)$, with $A$ a finite automaton, or a relational constraint $(x, t) \in R(T)$, with $t$ a concatenation of variables and $T$ a transducer (a 2-tape automaton), also written $x = T(t)$: the value of $x$ is an output of $T$ on the value of $t$. A conjunction $\Psi$ of atomic constraints is a *straight-line (SL) formula* if it can be written as $\Psi_0 \wedge \bigwedge_{i=1}^k \varphi_i$, where $\Psi_0$ is a conjunction of memberships and, for distinct variables $x_1, \dots, x_n$ with $n \ge k$, each $\varphi_i$ is $(x_i, t_i) \in R(T_i)$ and every variable $x_j$ occurring in $t_i$ has $j > i$. Its *language* $L(\Psi) \subseteq (\Sigma^*)^n$ is the set of tuples of values of $x_1, \dots, x_n$ over all solutions.

For classes of relations $\mathcal{C}$ and $\mathcal{S}$, two relations $I, E \in \mathcal{C}$ over the same tuple of variables are *$\mathcal{S}$-separable* if some $S \in \mathcal{S}$ has $I \subseteq S$ and $S \cap E = \emptyset$.

- An $n$-ary relation is *regular* (REG) here if it is a finite union of products $L_1 \times \dots \times L_n$ of regular languages.
- An $n$-ary relation is *$n$-PTL* if it is a finite Boolean combination of sets $(\Sigma^*)^n v_1 (\Sigma^*)^n \cdots v_k (\Sigma^*)^n$ with $v_1, \dots, v_k \in (\Sigma \cup \{\varepsilon\})^n$ and componentwise concatenation; each such set is the product, over the coordinates, of the piece languages of the component words of $v_1 \cdots v_k$, so for $n = 1$ these are the [piecewise testable languages](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md).

Then:

1. REG-separability of two SL formulas over the same variables is undecidable.
2. $n$-PTL-separability of two SL formulas over the variables $x_1, \dots, x_n$ is decidable.

If $L(\Psi) \subseteq S$ and $S \cap L(\Psi') = \emptyset$, then $\Psi \wedge \Psi'$ is unsatisfiable, so a separator certifies unsatisfiability; every string constraint is equisatisfiable with a conjunction of two SL formulas.

## Depends on

- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)
- [Piecewise testable languages](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md)

## Proof depends on

None.

## Expansion

This node still needs its proof broken down. Part 1 is the source's Theorem 2; the paragraph before it shows that REG-separability of arbitrary string constraints is undecidable, by comparing the constraint $(x, x) \in R(T)$ with the full relation, but that argument does not involve two SL formulas, and disjointness of two languages alone does not imply REG-separability, so the expansion must identify the reduction behind Theorem 2 for SL formulas. Part 2 (Theorem 11): solutions of an SL formula are encoded, as words $u_1 \# \cdots \# u_n$, by an ordered multi-pushdown automaton that guesses the source variables in its stacks and simulates the transducers from the last constraint to the first (Lemmas 8–9); $n$-PTL-separability of two SL formulas is equivalent to PTL-separability of the two encodings (Lemma 10). Ordered multi-pushdown languages form a full trio (Lemma 3) with effectively semilinear Parikh images (Lemma 5); for such classes PTL-separability is equivalent to the diagonal problem (Lemma 4), which is decidable (Theorem 6). The source leaves the complexity of part 2 open.

## Sources

- P. A. Abdulla, M. F. Atig, V. Dave and S. N. Krishna, "On the separability problem of string constraints", 31st International Conference on Concurrency Theory (CONCUR 2020), LIPIcs 171, Article 16, 2020, doi:[10.4230/LIPIcs.CONCUR.2020.16](https://doi.org/10.4230/LIPIcs.CONCUR.2020.16); full version arXiv:2005.09489v2, <https://arxiv.org/abs/2005.09489v2>: numbering of the published version, Section 2 (string constraints, SL formulas, Lemma 1, the separability problem), Section 3 (REG and Theorem 2), and Section 4 (piece languages and $n$-PTL, Lemmas 3–5 and 8–10, Theorems 6 and 11).
