# k-ordered quadratic word equations are NP-complete

A quadratic equation is k-ordered if both sides split into consecutive blocks over pairwise disjoint sets of at most k variables. For every fixed k, minimal solutions have length linear in the equation, and satisfiability is NP-complete.

Let $k \ge 1$ be a fixed integer. Let $A$ be an alphabet of constants with at least two letters (the standing convention of the source; in the decision problem below $A$ is part of the input). A quadratic word equation $\alpha = \beta$ over $A$ is **$k$-ordered** if there are pairwise disjoint sets of variables $X_1, \dots, X_\ell$, each with $|X_i| \le k$, and words $\alpha_i, \beta_i \in (X_i \cup A)^*$ such that $\alpha = \alpha_1 \alpha_2 \cdots \alpha_\ell$ and $\beta = \beta_1 \beta_2 \cdots \beta_\ell$. The bound $k$ limits the number of variables in each block, not the total number of variables. Solutions map variables to possibly empty words over $A$; a solution $h$ is minimal if no solution $h'$ has $|h'(\alpha)| < |h(\alpha)|$. Minimality ranges over all solutions, erasing ones included, so it is not the [length-minimality](../word-equation-algorithms/minimal-solutions/length-minimal-solution.md) among nonerasing solutions used for general word equations.

1. There is a constant $c_k$, depending only on $k$, such that every minimal solution $h$ of a $k$-ordered quadratic equation satisfies $|h(\alpha)| \le c_k \cdot |\alpha\beta|$; the source gives $c_k = 2^{2^{O(k^4)}}$.
2. For each fixed $k$, the problem of deciding whether a given $k$-ordered quadratic word equation, with the alphabet of constants part of the input, has a solution is NP-complete.

No uniform statement is made when $k$ is part of the input: with $k$ unbounded every quadratic equation is $k$-ordered with a single block. For instance $x_1 x_2 x_3 x_4 x_5 x_6 = x_3 x_2 x_1 x_6 x_4 x_5$ is 3-ordered but not 2-ordered.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Regular-ordered word equations are NP-complete](regular-ordered-equations-are-np-complete.md)

## Expansion

(1) The source's proof has three steps. First, variables occurring once can be replaced by their values in a minimal solution; the resulting equation has length less than $2|\alpha\beta|$ and a minimal solution of the same length (Proposition 2). Second, in the chains representation of a solution, that is, sequences of positions linked through the two occurrences of each variable, a satisfiable quadratic equation with $V$ twice-occurring variables has a solution in which every chain has length at most $2^{2^{O(V^4)}}$: a longer chain contains a repetition whose removal gives a shorter solution (Proposition 16, resting on the chain-shortening lemma, Lemma 11, which the source takes from MFCS 2017). Third, the source uses a length-based argument to divide a $k$-ordered equation, nondeterministically, into linearly many separate equations over the disjoint sets $X_i$, whose solutions combine into a solution of the whole. These separate equations are adjusted subinstances obtained from the lengths in a solution, not simply the defining factors $\alpha_i = \beta_i$: for example $xay = xay$ splits as $xa \mid y$ and $x \mid ay$ over the singleton sets $\{x\}, \{y\}$, but $xa = x$ and $y = ay$ have no solution. Each subinstance has at most $k$ variables, so its chains, and hence its minimal solutions, are short. These steps are internal to the source and have no pages of their own.

(2) By (1), a certificate of polynomial size is the list of the variable values of a minimal solution. For hardness, the strictly regular-ordered equations used for the hardness of regular-ordered equations have the same variables in the same order on both sides; cutting each side just after each variable (the last block also takes the trailing constants) exhibits them as 1-ordered, hence $k$-ordered for every $k \ge 1$. The source states this hardness in its introduction. The hard instances use four constants, and no claim is made for every fixed alphabet.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "Upper Bounds on the Length of Minimal Solutions to Certain Quadratic Word Equations", 44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019), LIPIcs 138, Article 44, pp. 44:1–44:15, 2019, <https://doi.org/10.4230/LIPIcs.MFCS.2019.44>, Section 1 (NP-hardness inherited from regular-ordered equations), Proposition 2 (removing once-occurring variables), Definition 6 and Lemma 11 (chains representation and chain shortening), Proposition 16 (chain length bound), Definition 18 ($k$-ordered equations and the example), Proposition 19 (length bound and membership in NP).
- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", MFCS 2017, LIPIcs 83, Article 18, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Abstract and Theorem 4 (hard instances with the same variables on both sides).
