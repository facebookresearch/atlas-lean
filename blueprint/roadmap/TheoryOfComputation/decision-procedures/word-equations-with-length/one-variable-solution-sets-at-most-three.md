# One-variable equations have at most three or infinitely many solutions

A word equation in one variable with constants has either infinitely many solutions or at most three, and three is attained. The empty word counts as a possible value of the variable.

Let $\Gamma$ be an alphabet of constants and $X$ a variable. A one-variable word equation is a pair $(U, V)$ of words over $\Gamma \cup \{X\}$; a solution is a constant-preserving morphism $h : (\Gamma \cup \{X\})^* \to \Gamma^*$ with $h(U) = h(V)$. It is determined by the word $h(X)$, which may be empty. If such an equation has only finitely many solutions, then it has at most three solutions.

The bound is attained: over $\Gamma = \{a, b\}$ the equation

$$XaXbXaabbabaXbabaabbab \;=\; abaabbabaXbabaabbXaXbX$$

has exactly the three solutions $h(X) \in \{\varepsilon,\ ab,\ abaabbab\}$. An equation with infinitely many solutions exists already with one occurrence of $X$ on each side: $Xab = abX$ has the solutions $h(X) = (ab)^i$, $i \ge 0$.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)

## Proof depends on

None.

## Expansion

The source's proof, with its ingredients:

1. *Shift to the empty solution (Lemma 13).* If the solution set is finite and nonempty with a shortest solution word $x_0$, then $x_0$ is a prefix of every solution word, and replacing $X$ by $x_0 X$ gives an equation whose solution words are $x_0^{-1} x_i$; one of them is empty. So it suffices to bound equations with the empty solution.
2. *Normal form (Section 4).* An equation with more than one solution has as many occurrences of $X$ on each side and can be written $(u_0 X u_1 \cdots X u_n,\ v_0 X v_1 \cdots X v_n)$ with constant words $u_i, v_i$ and $n \ge 1$. It is in *normal form* if (N1) it has the empty solution and at least one other zero-sum solution, (N2) $|u_0 \cdots u_i| < |v_0 \cdots v_i|$ for all $i < n$, and (N3) $|u_0 \cdots u_i| \le |v_0 \cdots v_{i-1}|$ for all $i \le n$. Here letters are interpreted as real numbers and a word is *zero-sum* if its letters add up to $0$; every word becomes zero-sum after a suitable renaming of the alphabet (Lemma 11), and zero-sum words form a free monoid (Lemma 12). Every nontrivial equation with the empty solution and another solution is equivalent, up to renaming letters, to an equation in normal form that is not longer (Lemma 15; its proof is omitted in the conference version). All solutions of an equation in normal form are zero-sum (Lemma 16).
3. *Heights and cuts (Lemmas 17–24).* With prefix sums, height (largest prefix sum) and area of words, the source shows that the prefix sums of the $u_i$ and of the $v_i$ are permutations of each other (Lemma 17), and that with at least three nonempty solutions all nonempty solutions have a common height determined by the equation (Lemma 18). It then cuts the equation at an index $k$ where $u_k$ is the first factor that is not zero-sum (Lemmas 21 and 22), compresses by a code when all factors are zero-sum (Lemma 20), and maps by a length-preserving morphism. This yields a strictly shorter equation with the empty solution and at least three, but finitely many, nonempty solutions.
4. *Conclusion (Theorem 25).* A shortest counterexample with the empty solution would then not be shortest, so there is none.

These lemmas are internal to the source. The example was checked by the source and, by brute force over $\{a, b\}$, has no further solution of length at most $12$.

## Sources

- Dirk Nowotka and Aleksi Saarela, "An Optimal Bound on the Solution Sets of One-Variable Word Equations and its Consequences", 45th International Colloquium on Automata, Languages, and Programming (ICALP 2018), LIPIcs 107, Article 136, pp. 136:1–136:13, 2018, <https://doi.org/10.4230/LIPIcs.ICALP.2018.136>, Theorem 25 (the bound), Example 5 (the equations above and their solution sets), Section 3 with Lemmas 11 and 12 (zero-sum words), Section 4 with the normal form (N1)–(N3) and Lemmas 13 and 15, Section 5 with Lemmas 16–19, Section 6 with Lemmas 20–24, Section 7 (proof of Theorem 25); preprint arXiv:1805.09535v1.
