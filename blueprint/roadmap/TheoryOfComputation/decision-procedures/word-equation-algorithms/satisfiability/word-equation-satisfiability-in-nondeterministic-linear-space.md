# Satisfiability of word equations in nondeterministic linear space


Satisfiability of word equations is decided in nondeterministic space linear in the number of bits of the input, for any fixed uniquely decodable encoding of its symbols.

Fix a uniquely decodable code that writes each letter and each variable as a fixed bitstring, so that the encoding of the two sides of an equation determines them, and let $m$ be the number of bits of the encoding of a word equation $U = V$ over letters $\Gamma$ and variables $\mathcal{X}$. There is a nondeterministic algorithm using $O(m)$ bits of space that accepts $U = V$ if and only if $U = V$ has a solution, a substitution of words over $\Gamma$ for the variables, possibly empty, with $\sigma(U) = \sigma(V)$. Hence the language of satisfiable word equations belongs to $\mathrm{NSPACE}(s)$ with $s(m) = m$.

The bound holds for every such code, in particular for a Huffman code of the input symbols. It improves the $O(n \log n)$-bit bound of the [polynomial-space algorithm](word-equation-satisfiability-in-pspace.md); the deterministic complexity remains between NP-hardness and PSPACE.


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [Nondeterministic space classes](../../../complexity-classes/time-and-space-complexity-classes/nspace.md)

## Proof depends on

- [Recompression operations are sound](../recompression/recompression-operations-are-sound.md)

## Expansion

The algorithm is a variant of recompression. Solutions may use letters outside the equation; they can be replaced by a fixed letter of the equation without changing lengths, and an equation without letters has the solution sending every variable to the empty word. A phase first fixes the alphabet $\Gamma$ of letters of the current equation, then performs block compression for $\Gamma$, after which no two consecutive letters of the solution word are equal letters of $\Gamma$, and then repeatedly guesses a partition $\Gamma_\ell, \Gamma_r$ of $\Gamma$ and performs $(\Gamma_\ell, \Gamma_r)$ pair compression, until every pair $ab$ of distinct letters $a \neq b$ of $\Gamma$ has had $a \in \Gamma_\ell$ and $b \in \Gamma_r$ for some partition; letters created during the phase are not considered. The end of the phase is guessed nondeterministically. Such a phase shortens the solution word $w$ to at most $(2|w| + 1)/3$ letters. In the proof, the partitions are those of a strategy that, in turn, halves four sums measuring how much popping and the extension of dependency intervals can increase the encoding; with each letter encoded through the interval of the input equation on which it depends, the size of the encoding at the start of every phase stays at most a constant times the input size. Letters are re-encoded with a Huffman code at each step, computable in linear bit space. Soundness of all steps follows from the soundness of the recompression operations.

The source also records the consequence that, since nondeterministic linear space accepts exactly the context-sensitive languages, the languages of satisfiable and of unsatisfiable word equations are context-sensitive.

This page becomes ready once the following are pages of their own: the shortening of a solution word by one phase (Jeż 2017, Lemma 2), the absence of equal consecutive letters after block compression (Lemma 4), the partition strategy halving the sums (1)–(4) (Lemma 10), the linear bound on the dependency-interval encoding (Lemmas 11 and 12), and the linear-space Huffman re-encoding (Lemma 6).

## Sources

- Artur Jeż, "Word Equations in Nondeterministic Linear Space", ICALP 2017, LIPIcs 80, Article 95 (2017), https://doi.org/10.4230/LIPIcs.ICALP.2017.95 (journal version: Journal of Computer and System Sciences 123 (2022), 122–142, https://doi.org/10.1016/j.jcss.2021.08.001), Theorem 3 (Section 2, algorithm LinWordEq) and its proof in Section 3.3, with Lemmas 1, 2, 6, 10, 11 and 12; the encoding convention and the context-sensitivity consequence are in Sections 1 and 2
- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Theorem 2 (Section 5), the earlier linear-space bound for a fixed number of variables
