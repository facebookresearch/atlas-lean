# Satisfiability of word equations is decidable

There is an algorithm that decides, for every word equation with constants over a free monoid, whether it has a solution. This is Makanin's theorem.

Let $A$ be a finite alphabet and $\mathcal{X}$ a finite set of variables. There is an algorithm that, given $A$ and a word equation $L = R$ with $L, R \in (A \cup \mathcal{X})^*$, decides whether there is a substitution $\sigma : \mathcal{X} \to A^*$, extended to a morphism fixing $A$, with $\sigma(L) = \sigma(R)$. Solutions may send variables to the empty word, and the alphabet is part of the input. The same holds for finite systems of word equations over an alphabet with at least two letters.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Satisfiability of word equations is in PSPACE](word-equation-satisfiability-in-pspace.md)
- [Systems of word equations over at least two letters reduce to one equation](system-of-word-equations-to-one-equation.md)

## Expansion

A polynomial-space decision procedure is in particular an algorithm, so decidability follows from the polynomial-space bound; when $A$ has letters not occurring in $L R$, satisfiability is unchanged, since such letters can be replaced by a letter of $L R$, and if $L R$ has no letters, the substitution sending every variable to the empty word is a solution. A finite system over an alphabet with two distinct letters has the same solutions as a single equation.

Historically the theorem was proved by G. S. Makanin (Mathematics of the USSR-Sbornik 32 (1977)) for free semigroups; Diekert's report presents the proof for free monoids and with regular constraints, following K. U. Schulz. It bounds the exponent of periodicity of a solution of minimal length, translates the equation into systems of boundary equations describing a guessed arrangement of the borders of the variables' images, transforms these under rules whose number of stored boundary equations is bounded through the convex chain condition, and decides reachability in the resulting finite search graph, in double exponential space.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Section 1 (statement of the satisfiability problem and of Makanin's result), Theorem 3.2, Theorem 4.12 and Theorem 5.7
- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Section 1, which recalls Makanin's theorem, and Theorem 1
