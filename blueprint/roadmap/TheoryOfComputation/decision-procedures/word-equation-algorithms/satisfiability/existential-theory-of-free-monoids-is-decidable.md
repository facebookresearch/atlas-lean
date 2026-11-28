# The existential theory of a free monoid on at least two letters is decidable

Whether a propositional combination of word equations and disequations with constants has a solution in a free monoid on at least two letters is decidable; equivalently, the existential theory of concatenation with constants is decidable.

Let $A$ be a finite alphabet with at least two letters. There is an algorithm that, given a formula $\exists x_1 \dots \exists x_k\, \Phi$, where $\Phi$ is built with $\land$, $\lor$ and $\lnot$ from atoms $L = R$ with $L, R \in (A \cup \{x_1, \dots, x_k\})^*$, decides whether there are words $w_1, \dots, w_k \in A^*$, possibly empty, making $\Phi$ true in the free monoid $A^*$ under $x_i \mapsto w_i$.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Elimination of a word disequation](disequation-elimination.md)
- [Systems of word equations over at least two letters reduce to one equation](system-of-word-equations-to-one-equation.md)
- [Satisfiability of word equations is decidable](word-equation-satisfiability-is-decidable.md)

## Expansion

Push negations to the atoms and replace each disequation by the positive formula of the disequation elimination, with fresh variables for each occurrence. Put the resulting positive formula in disjunctive normal form; it is satisfiable exactly when one of its conjunctions is, and each conjunction is a finite system of word equations. Since $A$ has two distinct letters, each system has the same solutions as a single word equation, whose satisfiability is decidable. The source proves the statement more generally, with regular constraints on the variables.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Section 1 (reduction of propositional formulas over word equations to a single equation) and Section 2.4 (Propositions 2.8 and 2.9 and the statement that the existential theory of equations over free monoids is decidable)
