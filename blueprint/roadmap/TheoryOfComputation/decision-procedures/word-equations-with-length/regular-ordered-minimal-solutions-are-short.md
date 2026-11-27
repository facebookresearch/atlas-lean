# Minimal solutions of regular-ordered equations are short

In a shortest solution of a regular-ordered word equation of length $n$, every variable is mapped to a word of length less than $n$, so shortest solutions have length $O(n^2)$. Quadratic equations in general can have exponentially long shortest solutions.

Following Day, Manea and Nowotka, a word equation is a pair $(\alpha, \beta)$ of *nonempty* words over $A \cup X$, and a solution is a morphism $h : (A \cup X)^* \to A^*$ fixing the constants (variables may be mapped to the empty word) with $h(\alpha) = h(\beta)$; the length of $h$ is $|h(\alpha)|$, and $h$ is *minimal* if no solution is shorter. Let $E$ be a regular-ordered equation $\alpha = \beta$ of length $n = |\alpha\beta|$. If $E$ has a solution and $h$ is a minimal solution, then

$$|h(x)| < n \quad \text{for every variable } x \text{ occurring in } E,$$

and consequently $|h(\alpha)| \in O(n^2)$.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)

## Proof depends on

None.

## Expansion

The proof works with sequences of equivalent positions. A position of the solution word $H = h(\alpha) = h(\beta)$ is described by a triple $(x, z, d)$: the $d$-th letter of the image of the occurrence of the variable $x$ on side $z$ (or a constant occurrence). A position on one side corresponds to the position of $H$ at the same index on the other side, and a position inside one occurrence of a twice-occurring variable $x$ also corresponds to the same offset inside the other occurrence of $x$. Starting at a position belonging to a constant or to a once-occurring variable, and alternating these two correspondences, gives a sequence $S_p$ of positions that all carry the same letter. The key lemma for quadratic equations (Lemma 14 of the source) says: if a sequence has a subsequence (not necessarily contiguous in the original sequence) that splits into two "similar" halves, then the corresponding factors can be cut out of the images of the variables to give a shorter solution, so $h$ is not minimal. For a regular-ordered equation, the order of the variables together with this lemma shows that each sequence meets each variable in at most one position. Every position of a minimal solution lies on one of the sequences, and the source's count of the sequences gives $|h(x)| < n$ (Proposition 17 and its proof). Summing over the at most $n$ symbols of $\alpha$ gives $|h(\alpha)| \in O(n^2)$. The intermediate lemma is part of the source's proof and has no page of its own.

The source shows the per-variable bound is optimal up to a constant factor with the equation $wcx = xcw$ for $w \in \{a, b\}^*$ and a third letter $c$: its minimal solution maps $x$ to $w$. *Arithmetic correction, computed here:* the source states $|h(x)| = |E| - 2$, but with $n = 2|w| + 4$ the minimal solution has $|h(x)| = |w| = (n - 4)/2$. Indeed $h(x) = w$ is a solution, and no shorter one exists: if $|h(x)| < |w|$, the two sides $wc\,h(x)$ and $h(x)\,cw$ have the same length, the first $c$ on the left is at position $|w| + 1$, and on the right the letter at position $|h(x)| + 1 \le |w|$ is $c$, while position $|h(x)| + 1$ on the left lies inside $w$, which contains no $c$. A brute-force check for $w = ab$ finds exactly the solutions $ab$, $abcab$, $abcabcab$ up to length $8$. This correction does not affect the stated bounds.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", 42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017), LIPIcs 83, Article 18, pp. 18:1–18:14, 2017, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Section 2 (equations as pairs of nonempty patterns, erasing substitutions, minimal solutions), Section 4: Lemma 14 (non-minimality from similar repetitions in sequences of positions), Proposition 17 (the bound $|h(x)| < n$ and its proof), and the paragraph after Proposition 17 (the example $wcx_1 = x_1cw$ with minimal solution $x_1 \mapsto w$, and the $O(|\alpha\beta|^2)$ length of minimal solutions).
