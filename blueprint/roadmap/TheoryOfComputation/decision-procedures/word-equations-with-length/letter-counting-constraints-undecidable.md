# Letter-counting constraints make word equations undecidable

Asking for a solution of a word equation whose letter counts satisfy a system of linear equations is undecidable. Length constraints, which only count all letters together, have open status.

The following decision problem is undecidable. An instance consists of a finite alphabet $A$ of constants, a single word equation $U=V$ over $A$, and a system of linear equations with integer coefficients in the letter counts $|\sigma(x)|_c$, where $x$ is a variable and $c\in A$. The question is whether a substitution $\sigma$ mapping variables to possibly empty words over $A$ solves the word equation and the linear system; $|w|_c$ denotes the number of occurrences of $c$ in $w$.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Commuting words are powers of a common word](commuting-words-are-powers-of-a-common-word.md)
- [Systems of word equations over at least two letters reduce to one equation](../word-equation-algorithms/satisfiability/system-of-word-equations-to-one-equation.md)
- [The halting problem is undecidable by multi-stack machines](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)
- [The halting problem is recognizable by multi-stack machines](../../computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)

## Expansion

The statement is the one the DLT 2024 survey attributes to Büchi and Senger, Corollary 4 (for exponent-sum and Parikh constraints). The sources state related exact variants. The existential theory of word equations, that is existentially quantified Boolean combinations of equations, becomes undecidable when extended by both predicates $|x|_a = |y|_a$ and $|x|_b = |y|_b$, and also when extended by $|x|_a = |y|_a$ together with the length equality $|x| = |y|$ (extended RP 2018, Corollaries 4.7 and 4.8, after Büchi and Senger). According to the same paper, the extension by the single predicate $|x|_a = |y|_a$ alone is open.

*Derived argument, written out here.* Fix any finite alphabet $A$ containing distinct letters $a,b$, and represent a natural number $n$ by $a^n$. This argument also gives undecidability for each such fixed alphabet, a stronger consequence than the general problem stated above; that uniformity is not attributed to the survey's theorem. The following are expressed by conjunctions of word equations and count equalities $|x|_c = |y|_c$, with auxiliary variables read existentially.

- *Unary words.* $ya = ay$ holds exactly when $y \in a^*$, by the commutation lemma ($a$ is primitive). Together with $|x|_a = |y|_a$ it says $y = a^{|x|_a}$; similarly for $b$.
- *Addition.* $z = xy$ with $x, y, z \in a^*$ says $|z| = |x| + |y|$.
- *Changing the letter.* $w\,ab = ab\,w$ holds exactly when $w \in (ab)^*$ ($ab$ is primitive). With $x \in a^*$, $y \in b^*$, $|x|_a = |w|_a$ and $|y|_b = |w|_b$ it says $|x| = |y|$.
- *Multiplication.* Let $x \in a^*$, $p = xb$, and require $zp = pz$. Since $p = a^{|x|}b$ is primitive, $z = p^j$ for some $j \ge 0$. Requiring $v \in b^*$ with $|v|_b = |z|_b$ and $r \in a^*$ with $|r|_a = |z|_a$ gives $v = b^j$ and $r = a^{|x| \cdot j}$. Converting $v$ to $a^j$ as above expresses $|r| = |x| \cdot j$.

The halting set for a fixed input is recognizable but undecidable, so by the Davis–Putnam–Robinson–Matiyasevich theorem it is Diophantine: membership $n \in S$ is solvability of $p(n, t_1, \dots, t_k) = 0$, which after moving negative terms to the other side is a conjunction of additions and multiplications over $\mathbb N$. The construction turns such a conjunction into a finite conjunction of word equations and count equalities that is satisfiable exactly when the Diophantine equation is solvable. The word equations combine into one equation with the same solutions (the reduction of systems to one equation, which needs two distinct letters), and each count equality is a linear equation in the counts. This gives the statement. Büchi and Senger define multiplication from the predicates $y = a^{|x|_a}$ and $y = b^{|x|_b}$; the construction above is a version of their encoding written with the commutation lemma, not a quotation of it.

## Sources

- Laura Ciobanu, "Word Equations, Constraints, and Formal Languages", Developments in Language Theory (DLT 2024), LNCS 14791, 2024, <https://doi.org/10.1007/978-3-031-66159-4_1>; read as arXiv:2406.02160v1, Section 2, problems (2) (WordEqn, EXP-SUM) and (3) (WordEqn, PARIKH), and the paragraph after the list of problems (undecidable in full generality, citing Büchi and Senger, Corollary 4; length constraints, problem (1), open). The published LNCS edition was not read.
- Laura Ciobanu and Georg Zetzsche, "Slice closures of indexed languages and word equations with counting constraints", 39th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2024), 2024, <https://doi.org/10.1145/3661814.3662134>; read as arXiv:2405.07911v1, Section 4 (the counting-constraint problem is undecidable in full generality; length constraints open).
- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Lemma 1 (commutativity equation), Lemma 2 (conjunctions as one equation), Section 3.1 (unary encoding; $\mathrm{Only}_a$ and $\mathrm{Only}_b$ model multiplication, after Büchi and Senger).
- Joel Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Extended Word Equations: The Boundary Between Decidability and Undecidability", arXiv:1802.00523v1, 2018 (extended version), Proposition 4.6 (equivalence of $Eq_a$ and $\mathrm{Only}_a$), Corollary 4.7 ($Eq_a$ and $Eq_b$), Corollary 4.8 ($Eq_a$ and length equality) and the remark after it (single predicate open).
- J. Richard Büchi and Steven Senger, "Definability in the Existential Theory of Concatenation and Undecidable Extensions of this Theory", *Zeitschrift für Mathematische Logik und Grundlagen der Mathematik* 34:337–342, 1988 (reprinted in *The Collected Works of J. Richard Büchi*, Springer, 1990, <https://doi.org/10.1007/978-1-4613-8928-6_37>), Corollary 4, cited through the sources above.
