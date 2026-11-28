# Solution sets of word equations are EDT0L

For a word equation over a free monoid and a chosen list of its variables, the set of words $\sigma(X_1)\#\cdots\#\sigma(X_k)$ over all solutions $\sigma$ is an EDT0L language, given by an automaton over endomorphisms that is computed in nondeterministic quasi-linear space.

Let $A$ be a finite alphabet, $\Omega$ a finite set of variables, $U = V$ a word equation with $U, V \in (A \cup \Omega)^*$, and $X_1, \dots, X_k$ distinct variables of $\Omega$, $k \ge 0$. Solutions are substitutions $\sigma : \Omega \to A^*$, possibly erasing, with $\sigma(U) = \sigma(V)$. Let $\# \notin A$ be a separator letter, let $A_\# = A \cup \{\#\}$, and let

$$
\mathrm{Sol} = \{ \sigma(X_1)\, \#\, \sigma(X_2)\, \# \cdots \#\, \sigma(X_k) : \sigma \text{ solves } U = V \} \subseteq A_\#^* ,
$$

where, by the encoding convention, for $k = 0$ each solution contributes the empty word. Then $\mathrm{Sol}$ is an [EDT0L language](edt0l-language.md) over the terminal alphabet $A_\#$, with $\#$ also as the start letter: there are an alphabet $C \supseteq A_\#$ and a nondeterministic finite automaton $\mathcal{A}$ with transitions labelled by endomorphisms of $C^*$ such that $\mathrm{Sol} = \{ \varphi(\#) : \varphi \in L(\mathcal{A}) \}$. The automaton is computed by a nondeterministic algorithm using $O(n \log n)$ bits of space, where $n$ is the input size $n = |UV| + |A| + |\Omega|$.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [EDT0L language](edt0l-language.md)

## Proof depends on

None.

## Expansion

The statement is the case of a single free monoid, with the identity involution on $A$, no constraints and a single equation, of the theorem of L. Ciobanu, V. Diekert and M. Elder (Theorem 2 of the ICALP 2015 paper), which covers Boolean formulas of equations with rational constraints over free products of free groups, finite groups and free monoids with involution; their input size counts $|A| + |\Omega|$ and the lengths of the atomic formulas, and the subset of variables is arbitrary.

Diekert's survey states the case in which $X_1, \dots, X_k$ are all the variables of the equation, under its convention $|A| + k \le |UV|$, together with two properties of its construction for that full solution set: the equation is solvable if and only if $L(\mathcal{A}) \neq \emptyset$, and it has infinitely many solutions if and only if $L(\mathcal{A})$ is infinite. These are not part of the statement above: for a proper subset of the variables, infinitely many solutions can give finitely many output words, as for $X = X$ over $\{a\}$ with $k = 0$.

This page becomes ready once the construction of the automaton and its soundness and completeness are pages of their own: the preprocessing, initial equation and extended equations (Ciobanu, Diekert and Elder, Sections 2.1–2.3), the compression and substitution arcs and the quasi-linear-space construction (Sections 2.5–2.7), the forward property and compression steps (Sections 2.8–2.9), and the generalisation to Theorem 2 in Part II.

## Sources

- Laura Ciobanu, Volker Diekert, Murray Elder, "Solution Sets for Equations over Free Groups are EDT0L Languages", ICALP 2015, LNCS 9135, 134–145 (2015), https://doi.org/10.1007/978-3-662-47666-6_11; read as arXiv:1502.03426v2, https://arxiv.org/abs/1502.03426v2, Theorem 2, the free-monoid case, with Definition 1 (Section 1.3), Sections 2.1–2.9 and Part II
- Volker Diekert, "More Than 1700 Years of Word Equations", Algebraic Informatics (CAI 2015), LNCS 9270, 22–28 (2015), https://doi.org/10.1007/978-3-319-23021-4_2; read as arXiv:1507.03215v1, https://arxiv.org/abs/1507.03215v1, Section "Rational sets of endomorphisms"
- Artur Jeż, "Solving Word Equations (And Other Unification Problems) by Recompression (Invited Talk)", CSL 2020, LIPIcs 152, Article 3 (2020), https://doi.org/10.4230/LIPIcs.CSL.2020.3, Theorem 12 and the paragraph before it (Section 3)
