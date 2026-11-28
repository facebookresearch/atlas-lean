# One-variable word equations in near-linear time

A description of all solutions of a word equation with a single variable, occurring any number of times, can be computed deterministically in time $O(n + \#_X \log n)$, where $n$ is the length of the equation and $\#_X$ the number of occurrences of the variable, and in time $O(n)$ on a RAM.

Let $\Gamma$ be an alphabet of constants whose letters are identified with consecutive integers, so that pairs of letters can be sorted by radix sort, and let $\mathcal A = \mathcal B$ be a one-variable word equation, $\mathcal A, \mathcal B \in (\Gamma \cup \{X\})^*$, with $n = |\mathcal A| + |\mathcal B|$ and $\#_X = n_{\mathcal A} + n_{\mathcal B}$ occurrences of $X$. A solution is a substitution $S(X) \in \Gamma^*$ with $S(\mathcal A) = S(\mathcal B)$.

1. There is a deterministic algorithm that, for $n \ge 1$, in time $O(n + \#_X \log n)$, computes a description of all solutions $S$ with $S(X) \ne \varepsilon$. An equation with identical sides is reported as having every substitution as a solution. Otherwise, after the normalisation described in the Expansion, the solutions are determined by their lengths and are reported by length, and an infinite family of solutions is represented by a finite description rather than listed.
2. With additional data structures (suffix arrays with constant-time longest-common-prefix queries) and a finer analysis, the running time is $O(n)$ in the RAM model.

The empty substitution $S(X) = \varepsilon$ is excluded by the algorithm and can be tested separately in time $O(n)$; the empty equation ($n = 0$) has identical sides.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [Suffix array](../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Longest common prefix length](../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/lcp.md)

## Proof depends on

None.

## Expansion

*Normal form (Section 2 of the source).* Consider only nonempty solutions. Cancel equal leading symbols and equal trailing symbols; if two different constants become leading (or trailing) the equation has no solution. If the remaining equation is trivial, every substitution is a solution; if one side has become empty, the other side must evaluate to the empty word, so no nonempty solution exists unless the other side is empty too. Otherwise, after possibly exchanging the sides, one side begins with a constant and the other with $X$, and the equation can be written as $A_0 X A_1 \cdots X A_{n_{\mathcal A}} = X B_1 \cdots X B_{n_{\mathcal B}}$ with $A_0 \ne \varepsilon$. For this form, every nonempty solution is $S(X) = A_0^k A$ for some $k \ge 0$ and a prefix $A$ of $A_0$, so it is determined by its length (Lemma 2). Moreover, for each letter $a$, the solutions with $S(X) \in a^+$ are none, exactly one, or all of them, and which case holds is decided in time $O(n)$ (Lemma 11).

*Algorithm.* The algorithm is a deterministic specialisation of recompression. A phase compresses every maximal block $a^\ell$ of a letter into a fresh letter and every pair $ab$ of distinct letters into a fresh letter. To make pairs and blocks that cross the boundary of $X$ compressible, $X$ is replaced by $a^\ell X$ (or $X a^\ell$), after testing whether $S(X) = a^\ell$ is itself a solution, which is reported if so (Lemmas 1, 4, 6 and 7). The other solutions are transported in the sense of the source's Definition 1: each solution $S$ that is not reported has the form $S(X) = u\, h(S'(X))\, v$ for a solution $S'$ of the compressed equation, where $h$ expands the fresh letter back into the pair or block and $u, v$ are words computed by the subprocedure, and conversely each solution $S'$ of the compressed equation gives an unreported solution of this form (Lemmas 3, 5 and 8, Lemma 8 for the compression of blocks of all letters; for the popping and cutting steps of Lemmas 4, 6 and 7, which only preserve solutions, $h$ is the identity). Each phase runs in linear time, and the explicit words between occurrences of $X$ shrink by a constant factor per phase while they are long (Lemma 10); the $\#_X \log n$ term pays for the short words (Theorem 1). Section 4 of the source adds suffix arrays with longest-common-prefix queries, storage of short words as factors of long ones, and a refined analysis of the tests to obtain $O(n)$ in the RAM model. These lemmas are internal to the source.

## Sources

- Artur Jeż, "One-Variable Word Equations in Linear Time", *Algorithmica* 74(1):1–48, 2016, <https://doi.org/10.1007/s00453-014-9931-3> (open access), Section 1 (note on the computational model), Section 2 (normal form of the equation, exclusion of the empty solution), Definition 1 (preserving and implementing solutions), Lemmas 1–8, 10 and 11, Theorem 1 (running time $O(|\mathcal A| + |\mathcal B| + (n_{\mathcal A} + n_{\mathcal B}) \log(|\mathcal A| + |\mathcal B|))$, all solutions reported), Abstract and Section 4 (linear time in the RAM model). Preprint: arXiv:1302.3481v2. Conference version: ICALP 2013, LNCS 7966, <https://doi.org/10.1007/978-3-642-39212-2_30>.
