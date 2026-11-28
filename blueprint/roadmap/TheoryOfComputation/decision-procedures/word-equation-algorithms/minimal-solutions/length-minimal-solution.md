# Length-minimal solution of a word equation

A nonerasing solution of a word equation is length-minimal when no other nonerasing solution has a shorter solution word. Size and periodicity bounds for word equations are stated for these solutions.

Let $A$ be a finite alphabet of letters and $\mathcal{X}$ a finite set of variables disjoint from $A$. A word equation $U = V$ is a pair of words $U, V \in (A \cup \mathcal{X})^*$, and its size is $n = |U| + |V|$. A substitution is a monoid morphism $\sigma : (A \cup \mathcal{X})^* \to A^*$ with $\sigma(a) = a$ for every $a \in A$; it is a solution of $U = V$ when $\sigma(U) = \sigma(V)$, and the word $\sigma(U)$ is then its solution word.

A solution $\sigma$ is nonerasing when $\sigma(X) \neq \varepsilon$ for every variable $X$ that occurs in $UV$; variables not occurring in $UV$ are sent to $\varepsilon$ by convention. A nonerasing solution $\sigma$ is length-minimal when

$$
|\sigma(U)| \le |\sigma'(U)| \quad \text{for every nonerasing solution } \sigma' \text{ of } U = V .
$$

The length of a length-minimal solution, usually written $N$, is $|\sigma(U)|$.

Restricting to nonerasing solutions does not change satisfiability: an equation has a solution exactly when, for some set $Y$ of its variables, the equation obtained by deleting every occurrence of the variables in $Y$ has a nonerasing solution. An equation that has a nonerasing solution has at least one length-minimal solution, and only finitely many.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Occurring variable's image is no longer than the evaluated word](../../string-constraints-and-word-equations/ordinary-word-equations/length-le-eval-word-of-mem.md)

## Expansion

The definitions and the reduction to nonerasing solutions (guess which variables are empty and delete them) are the source's. The remaining two remarks are elementary. Existence: the lengths $|\sigma(U)|$ of nonerasing solutions form a nonempty set of natural numbers, which has a least element. Finiteness: in a nonerasing solution with $|\sigma(U)| = |\sigma(V)| = N$, each occurring variable $X$ occurs in $U$ or in $V$, so $|\sigma(X)| \le N$ because an occurring variable's image is no longer than the evaluated word, and over the finite alphabet $A$ there are finitely many such assignments.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Section 2 (paragraphs defining substitutions, solutions and length-minimal solutions, with the exclusion of erasing solutions and the reduction to it)
- Artur Jeż, "Word Equations in Nondeterministic Linear Space", ICALP 2017, LIPIcs 80, Article 95 (2017), https://doi.org/10.4230/LIPIcs.ICALP.2017.95 (journal version: Journal of Computer and System Sciences 123 (2022), 122–142, https://doi.org/10.1016/j.jcss.2021.08.001), Section 2, "Notions"
