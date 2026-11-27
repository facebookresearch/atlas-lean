# Approximate sequential uniformization of rational relations is undecidable

For the Levenshtein, longest-common-subsequence and Damerau–Levenshtein edit distances, no algorithm decides whether a rational relation given by a finite transducer has a uniformizer within bounded edit distance of some sequential function.

**Definitions.** A finite-state transducer (as in [rational relations and transducers](../rational-relations-and-transducers.md)) recognizes a rational relation $R \subseteq A^* \times B^*$; a function is *sequential* if it is recognized by an input-deterministic transducer (see [sequential and subsequential functions](../sequential-and-subsequential-functions.md)). An *edit distance* $d$ on $B^*$ is the least number of allowed edit operations rewriting one word into another, and $\infty$ if there is none: $d_{lcs}$ allows insertions and deletions, $d_l$ (Levenshtein) insertions, deletions and substitutions, and $d_{dl}$ (Damerau–Levenshtein) also swaps of adjacent letters. For partial functions $f_1, f_2 : A^* \to B^*$,

$$
d(f_1, f_2) = \sup \{ d(f_1(w), f_2(w)) : w \in \mathrm{dom}(f_1) \} \text{ if } \mathrm{dom}(f_1) = \mathrm{dom}(f_2), \qquad d(f_1, f_2) = \infty \text{ otherwise}.
$$

A *uniformizer* of $R$ is a function $U$ with $\mathrm{dom}(U) = \mathrm{dom}(R)$ and $(u, U(u)) \in R$ for all $u \in \mathrm{dom}(R)$. The relation $R$ is *$d$-approximately uniformizable* if there are a uniformizer $U$ of $R$ and a sequential function $f$ with $d(U, f) < \infty$; equivalently, there are a sequential $f$ and $k \in \mathbb{N}$ such that every $u \in \mathrm{dom}(R)$ has some $(u, v) \in R$ with $d(v, f(u)) \le k$.

**Theorem.** For each $d \in \{d_l, d_{lcs}, d_{dl}\}$ it is undecidable, given a finite transducer recognizing a rational relation $R$, whether $R$ is $d$-approximately uniformizable.

The exact version, whether a rational relation has a sequential uniformizer, is undecidable as well, and the reduction below shows both at once. The case of the Hamming distance is left open by the source, as is the letter-to-letter setting. By contrast, the source proves that approximate functionality and approximate determinisation of transducers are decidable for several classical distances, including the Hamming and Levenshtein distances.

## Depends on

- [Rational relations and transducers](../rational-relations-and-transducers.md)
- [Sequential and subsequential functions](../sequential-and-subsequential-functions.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Reduce from the Post correspondence problem for morphisms $\varphi_1, \varphi_2 : \{1, \dots, k\}^* \to B^*$. The relation $R$ takes inputs $w_1 \# w_2 \# \cdots w_m \# X$ with $w_i \in \{1, \dots, k\}^*$ and a final letter $X \in \{a, b\}$: for $X = a$ the only output is $\varphi_1(w_1) \# \cdots \varphi_1(w_m) \#$, and for $X = b$ every $v_1 \# \cdots v_m \#$ with $v_i \neq \varphi_2(w_i)$ for all $i$ is an output; $R$ is rational. If the instance has no solution, outputting $\varphi_1(w_1) \# \cdots \varphi_1(w_m) \#$ is a sequential uniformizer. If $w$ is a solution, a sequential $f$ at bounded distance from a uniformizer would, on the inputs $(w\#)^\ell a$ and $(w\#)^\ell b$, produce outputs that differ only after a common prefix; by the triangle inequality some output for $X = b$ would then lie within bounded distance of $(\varphi_1(w)\#)^\ell$, and for large $\ell$ some block $\# v_i \#$ would be unedited, forcing $v_i = \varphi_1(w) = \varphi_2(w)$, a contradiction.

## Sources

- E. Filiot, I. Jecker, K. Madnani and S. Sunny, "Approximate Problems for Finite Transducers", in *52nd International Colloquium on Automata, Languages, and Programming (ICALP 2025)*, LIPIcs 334, paper 155, pp. 155:1–155:19, 2025, doi:[10.4230/LIPIcs.ICALP.2025.155](https://doi.org/10.4230/LIPIcs.ICALP.2025.155). Read in arXiv:2504.17299v1 ([arXiv](https://arxiv.org/abs/2504.17299v1)), whose numbering is used here: Table 1 and Definition 1 in Section 2 (edit distances and the distance between functions), Definition 39 (approximate uniformization), Theorem 40 with its proof, and Section 6 (open cases).
