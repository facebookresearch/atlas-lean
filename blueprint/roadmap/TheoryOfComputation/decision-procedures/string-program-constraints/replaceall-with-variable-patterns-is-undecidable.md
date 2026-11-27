# replaceAll with variable patterns is undecidable

If the pattern argument of replaceAll may be a string variable, satisfiability of straight-line replaceAll constraints is undecidable, even with a single variable pattern, single-letter patterns elsewhere, and two membership constraints.

In the class $\mathrm{SL}[\mathrm{replaceAll}]$ of [straight-line replaceAll constraints](straight-line-replaceall-constraints.md), under the [leftmost-longest replaceAll](leftmost-longest-replaceall.md) semantics, a pattern variable assigned a word $w$ is read as the regular expression denoting $\{w\}$. There is no algorithm that decides, given a finite alphabet and a formula of $\mathrm{SL}[\mathrm{replaceAll}]$ over it, whether the formula is satisfiable, already for formulas in which exactly one replaceAll term has a variable pattern, every other pattern is a single letter, and the regular constraint consists of two memberships. The alphabet is part of the input: the reduction adds one fresh letter per domino and one more letter.

## Depends on

- [Straight-line replaceAll constraints](straight-line-replaceall-constraints.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Given dominoes $(\alpha_1, \beta_1), \dots, (\alpha_N, \beta_N)$ over $\Sigma$, add fresh letters $1, \dots, N$ and $\sharp$, and take

$$
\bigwedge_{i=1}^N \bigl(x_i = \mathrm{replaceAll}(x_{i-1}, i, \alpha_i) \wedge y_i = \mathrm{replaceAll}(y_{i-1}, i, \beta_i)\bigr) \wedge z = \mathrm{replaceAll}(x_N, y_N, \sharp),
$$

with $y_0$ the same variable as $x_0$, $x_0 \in (1 + \dots + N)^+$ and $z \in \sharp$. The source prints $y_0$ without defining it, while its proof uses the same index word on both sides; reading $y_0$ as an alias of $x_0$ is the interpretation its proof requires. If $x_0 = i_1 \cdots i_K$, the first conjuncts substitute $\alpha_i$, respectively $\beta_i$, for each index letter, so $x_N = \alpha_{i_1} \cdots \alpha_{i_K}$ and $y_N = \beta_{i_1} \cdots \beta_{i_K}$, words over $\Sigma$. Then $\mathrm{replaceAll}(x_N, y_N, \sharp) = \sharp$ iff $x_N = y_N$: if $y_N$ is nonempty, every match is replaced by $\sharp$ and the letters between matches are kept, so the result is $\sharp$ only when $x_N$ is a single match; if $y_N = \varepsilon$, the pattern matches the empty word, and the result is $\sharp$ exactly when $x_N = \varepsilon$ (otherwise $\sharp$ is inserted around every letter of $x_N$). Hence the formula is satisfiable iff the instance has a solution. The source states the Post correspondence problem with nonempty words, for which the case $y_N = \varepsilon$ does not arise; the computation above shows the reduction also works when words may be empty.

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Section 4, Proposition 4.1, and Appendix A (its proof), with Definition 3.3 for the case of an empty pattern.
