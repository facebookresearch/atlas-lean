# Non-cross equations with one repeated variable are in P

If both sides of a word equation are non-cross and every variable except one fixed variable occurs at most once, satisfiability is decidable in polynomial time. This class contains all one-variable equations.

Fix a variable $x$. Let $\mathcal D$ be the class of word equations $\alpha = \beta$ with $\alpha, \beta \in (\Sigma \cup X)^*$ such that $\alpha$ and $\beta$ are non-cross and every variable other than $x$ occurs at most once in $\alpha\beta$ in total (the variable $x$ may occur any number of times). Solutions map variables to possibly empty words over the constants. The problem of deciding whether a given equation of $\mathcal D$ has a solution is in P.

As a special case, the pattern-searching problem is in P: given words $\alpha, \beta$ over the constants and the single variable $x$, decide whether some value of $x$ makes $\alpha$ a factor of $\beta$; this is satisfiability of $x_2 \alpha x_3 = \beta$, an equation of $\mathcal D$.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)

## Proof depends on

None.

## Expansion

If both sides contain at least two variables, the source refers to the earlier result of Manea, Nowotka and Schmid for one-repeated-variable equations with a non-repeated variable on each side. So assume $\mathrm{var}(\alpha) = \{x\}$. The source proves completely the case $\alpha = x u_1 x u_2 \cdots u_k x$ and $\beta = y v_0 x v_1 \cdots x v_k z$ with constant words $u_i, v_i$ and single variables $y, z$, and states that the general case, with regular patterns in place of $y$ and $z$, is a straightforward adaptation. The steps are as follows.

1. A solution with prescribed lengths of $x, y, z$ can be found or excluded in time polynomial in those lengths by filling the positions, so it suffices to bound the minimal solutions polynomially; it is enough to bound $|g(x)|$.
2. If, in a minimal solution $g$ with $|g(x)| > |\alpha\beta|$, two constant factors $u_i$ and $v_j$ overlap, then $g(x)$ has the short period $|v_j| - \ell$ and so has the form $(st)^p s$, where $st$ is the suffix of $v_j$ of that length and $s$ is a prefix of $st$; for large $p$, replacing $g(x)$ by $(st)^{p-1} s$ gives another solution, contradicting minimality.
3. Otherwise all occurrences of $g(x)$ overlap, and the solutions correspond to solutions of the system $x = x_0 v_0 x_1 = x_1 u_1 x_2 = x_2 v_1 x_3 = \cdots = x_{2k} v_k x_{2k+1}$. The source splits it into systems in which equations such as $A_1 x = y B_1,\ A_2 A_1 x = y B_1 B_2,\ \dots,\ A_k \cdots A_1 x = y B_1 \cdots B_k$ appear. Such a system is analysed by factoring out the first equation: every further equation becomes a conjugacy equation $A_i \cdots A_2\, w = w\, B_2 \cdots B_i$ in one unknown word $w$. By the solution of the conjugacy equation, $w = (u_i v_i)^{p_i} u_i$ with $u_i v_i$ primitive, $A_i \cdots A_2 = (u_i v_i)^{q_i}$ and $B_2 \cdots B_i = (v_i u_i)^{q_i}$. Since $w$ is long, the periodicity lemma of Fine and Wilf (in Mathlib as [the periodicity lemma](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/List/PeriodicityLemma.lean#L184 "List.HasPeriod.gcd")) forces all the primitive words $u_i v_i$ to coincide.
4. With a common primitive period of length at most $|\alpha\beta|$, many repetitions in $g(x)$ again allow a shorter solution, so minimal solutions have polynomial length.

The general case of regular patterns $\beta', \beta''$ in place of $y, z$ is asserted, not written out, in the source.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", 42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017), LIPIcs 83, Article 18, pp. 18:1–18:14, 2017, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Theorem 22 and the discussion following it (Section 5), and Section 1 (the pattern-searching consequence). The proof is in the appendix of the preprint arXiv:1702.07922v2 (proof of Theorem 22, with the Fine–Wilf lemma, the conjugacy-equation lemma and the lemma on the system $A_i \cdots A_1 x = y B_1 \cdots B_i$).
- Florin Manea, Dirk Nowotka and Markus L. Schmid, "On the Solvability Problem for Restricted Classes of Word Equations", Developments in Language Theory (DLT 2016), LNCS 9840, pp. 306–318, 2016, <https://doi.org/10.1007/978-3-662-53132-7_25>; read as the author preprint <http://www.mlschmid.de/preprints/conferences/2016_DLT_preprint.pdf>, Theorem 2 (one repeated variable with a non-repeated variable on each side).
