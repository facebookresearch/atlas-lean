# Recompression algorithm for word equations

Recompression is a nondeterministic procedure for word equations that compresses pairs of letters and maximal blocks of a guessed solution word directly on the equation, popping letters out of variables so that the compressed pairs and blocks never cross a variable boundary.

Let $U = V$ be a word equation over letters $\Gamma$ and variables $\mathcal{X}$, and let $\sigma$ be a nonerasing solution (see [length-minimal solutions](../minimal-solutions/length-minimal-solution.md)); the guesses below are described as if $\sigma$ were known.

- For a factor $u \in \Gamma^+$ of $\sigma(U)$ (or of $\sigma(V)$), an occurrence of $u$ is explicit if it comes from a factor $u$ of $U$ (or $V$), implicit if it lies inside $\sigma(X)$ for an occurrence of a variable $X$, and crossing otherwise. A pair $ab$ of letters with $a \neq b$ is crossing if it has a crossing occurrence. A letter $a$ has a crossing block if the two-letter factor $aa$ has a crossing occurrence.
- A maximal block of $a$ is an occurrence of $a^\ell$, $\ell \ge 1$, in $\sigma(U)$ that extends neither to the left nor to the right by $a$. A fresh letter is a letter not occurring in the current equation.

The procedure uses the following operations.

- Pair compression of $ab$, $a \neq b$: replace every explicit occurrence of $ab$ in $U$ and $V$ by a fresh letter $c$; for a noncrossing pair this replaces every occurrence of $ab$ in the solution word.
- Block compression of $a$: for each length $\ell \ge 2$ of a maximal block of $a$, replace every explicit maximal block $a^\ell$ by a fresh letter $a_\ell$.
- Popping, for a partition $\Gamma = \Gamma_\ell \sqcup \Gamma_r$ of the letters present: for each variable $X$, guess the first letter $b$ of $\sigma(X)$; if $b \in \Gamma_r$, replace every occurrence of $X$ by $bX$, and remove $X$ if its remaining value is guessed to be empty; then act symmetrically on the last letter $a$, replacing $X$ by $Xa$ if $a \in \Gamma_\ell$. Afterwards the pairs in $\Gamma_\ell \Gamma_r$ are compressed by pair compression.
- Cutting prefixes and suffixes: for each variable $X$, let $a$ and $b$ be the first and last letters of $\sigma(X)$ and guess $\ell_X \ge 1$ and $r_X \ge 0$ with $\sigma(X) = a^{\ell_X}\, w\, b^{r_X}$, where $a^{\ell_X}$ is the maximal $a$-prefix and $b^{r_X}$ the maximal $b$-suffix; when $\sigma(X)$ is a single block $a^{\ell_X}$, take $r_X = 0$ and $w = \varepsilon$. Replace every occurrence of $X$ by $a^{\ell_X} X b^{r_X}$, and remove $X$ if $w = \varepsilon$. Afterwards no letter has a crossing block, and block compression is applied to every letter.

A phase runs cutting of prefixes and suffixes with block compression, computes the set of letters present, and then twice guesses a partition of these letters and runs popping with pair compression. The procedure repeats phases while $|U| > 1$ or $|V| > 1$; when both sides have length at most $1$ (each side empty, a letter or a variable), it decides the remaining equation directly. The fresh letters can be read as nonterminals of a straight-line program ($c \to ab$, $a_\ell \to a^\ell$) that generates the solution word.

## Depends on

- [Length-minimal solution of a word equation](../minimal-solutions/length-minimal-solution.md)

## Proof depends on

None.

## Expansion

This page defines the procedure; its soundness, completeness and resource bounds are stated in [Soundness and completeness of recompression](recompression-is-sound-and-complete.md). One of the two partitions of a phase is chosen to shorten the solution word, the other to shorten the equation.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Definition 1 and Algorithms 1–7 (PairCompNCr, BlockCompNCr, Pop, PairComp, CutPrefSuff, BlockComp, WordEqSat) in Sections 2 and 3; the straight-line-program reading is in Section 2, "Fresh letters"
- Artur Jeż, "Word Equations in Nondeterministic Linear Space", ICALP 2017, LIPIcs 80, Article 95 (2017), https://doi.org/10.4230/LIPIcs.ICALP.2017.95 (journal version: Journal of Computer and System Sciences 123 (2022), 122–142, https://doi.org/10.1016/j.jcss.2021.08.001), Section 2, which restates block compression and $(\Gamma_\ell, \Gamma_r)$ pair compression
