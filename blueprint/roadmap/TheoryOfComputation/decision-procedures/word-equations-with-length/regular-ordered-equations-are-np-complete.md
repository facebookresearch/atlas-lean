# Regular-ordered word equations are NP-complete

Deciding whether a regular-ordered word equation has a solution is NP-complete. Hardness holds already when both sides contain exactly the same variables in the same order; membership in NP follows because minimal solutions have polynomial length.

Let the input be a regular-ordered word equation $\alpha = \beta$ with nonempty sides over an alphabet of constants given with the input, of size $n = |\alpha\beta|$; solutions map variables to possibly empty words over the constants. The problem of deciding whether $\alpha = \beta$ has a solution is NP-complete. NP-hardness holds already for strictly regular-ordered equations, that is, when both sides contain exactly the same variables, in the same order.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Minimal solutions of regular-ordered equations are short](regular-ordered-minimal-solutions-are-short.md)

## Expansion

Membership: if the equation has a solution it has one in which every variable is mapped to a word of length less than $n$, so a certificate of polynomial size is the list of these words, checked by substituting and comparing.

Hardness goes through the problem REP (rewriting with programmed rules): given words $u_{\mathrm{start}}, u_{\mathrm{end}}$ and an ordered list of rules $w_i \to w'_i$ ($1 \le i \le r$), decide whether $u_{\mathrm{end}}$ arises from $u_{\mathrm{start}}$ by applying each rule once, in order, each time to some occurrence of $w_i$. REP is NP-complete by a reduction from 3-PARTITION with numbers written in unary, which is NP-complete in the strong sense: for numbers $k_1, \dots, k_{3m}$ with sum $ms$, take $u_{\mathrm{start}} = b^m$, $u_{\mathrm{end}} = (a^s b c^3)^m$ and the $r = 3m$ rules $b \to a^{k_i} b c$. The unary encoding is what makes this reduction polynomial; the NP-completeness of 3-PARTITION with binary numbers does not suffice. For an instance of REP, the source first builds an equation $\alpha_\mu = \beta_\mu$ and shows that REP holds exactly when it has an *overlapping* solution, one in which each rule application is encoded in the period of a variable's image. It then builds the equation

$$x_1 \# x_2 \# x_3\, w_1\, x_4 \# x_5 \# x_6\, w_2 \cdots x_{3r+1} \# x_{3r+2} \# x_{3r+3}\, \# u_{\mathrm{end}} \;=\; \# u_{\mathrm{start}}\, x_1 \# x_2 \# x_3\, w'_1\, x_4 \# x_5 \# x_6 \cdots w'_r\, x_{3r+1} \# x_{3r+2} \# x_{3r+3},$$

which is strictly regular-ordered and has an arbitrary solution exactly when $\alpha_\mu = \beta_\mu$ has an overlapping solution; the extra separators $\#$ force the overlaps. The hard instances built this way use only the four constants $a, b, c, \#$. This is read off the construction; the source does not state hardness over a fixed alphabet separately.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", 42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017), LIPIcs 83, Article 18, pp. 18:1–18:14, 2017, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Abstract (hardness even when the sides contain exactly the same variables) and Section 1 (the reduction uses one occurrence of each variable per side, in the same order on both sides), Section 2 (nonempty sides, 3-PARTITION strongly NP-complete), Theorem 4 (NP-hardness), Problem 5 and Lemma 7 (REP), Definition 8 and Lemmas 9–11 (the equations and their correctness), Theorem 18 (membership in NP via Proposition 17), Section 6 (NP-completeness). The proofs of Lemmas 7 and 9 are in the appendix of the preprint arXiv:1702.07922v2.
