# Quadratic, regular and regular-ordered word equations

Restricted classes of word equations are defined by how often, and in which order, the variables occur on the two sides: quadratic (each variable at most twice), regular (at most once per side), regular-ordered (regular with the shared variables in the same order), non-cross, and one-variable equations.

Let $A$ be an alphabet of constants and $X$ a set of variables, and let $\alpha = \beta$ be a word equation with $\alpha, \beta \in (A \cup X)^*$. For a word $\gamma$ and a variable $x$ write $|\gamma|_x$ for the number of occurrences of $x$ in $\gamma$, and $\mathrm{var}(\gamma)$ for the set of variables occurring in $\gamma$. The equation $\alpha = \beta$ is

- **quadratic** if $|\alpha\beta|_x \le 2$ for every variable $x$;
- **regular** if $|\alpha|_x \le 1$ and $|\beta|_x \le 1$ for every variable $x$ (so every regular equation is quadratic);
- **regular-ordered** if it is regular and there are no variables $x, y$ such that $x$ occurs before $y$ in $\alpha$ while $y$ occurs before $x$ in $\beta$; equivalently, deleting from $\alpha$ and from $\beta$ all constants and all variables that occur only once in $\alpha\beta$ leaves the same word;
- **strictly regular-ordered** if it is regular-ordered and every variable of $\alpha\beta$ occurs in both $\alpha$ and $\beta$ (so $\mathrm{var}(\alpha) = \mathrm{var}(\beta)$);
- **non-cross** if neither side contains, between two occurrences of a variable $x$, an occurrence of a variable other than $x$;
- **one-variable** if $\mathrm{var}(\alpha\beta)$ has at most one element; the variable may occur any number of times.

For example, $x_1 a x_2 x_3 b = x_1 a x_2 b x_3$ is strictly regular-ordered, $x_1 a = x_1 x_2$ is regular-ordered but not strictly, $x_1 a x_3 x_2 b = x_1 a x_2 b x_3$ is regular but not regular-ordered, and $xaby = ybax$ is regular while $xabx = ybay$ is quadratic but not regular. Lin and Majumdar call an equation *oriented* if some total order on the variables is respected by the occurrences of variables on each side; a regular equation is oriented exactly when it is regular-ordered.

The sources differ on whether a side may be empty: Day, Manea and Nowotka (MFCS 2017) take both sides nonempty, $(\alpha, \beta) \in (A \cup X)^+ \times (A \cup X)^+$, while Day and Manea (ToCS) and Day et al. (RP 2018) allow $(A \cup X)^*$. Results imported from a source keep that source's convention, and the pages using them say so.

## Depends on

- [Ordinary word equation](../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)

## Proof depends on

None.

## Expansion

The two formulations of regular-ordered agree. A variable occurring only once in $\alpha\beta$ cannot be part of an inverted pair, and two variables occurring on both sides occur in the same order on both sides exactly when they form no inversion; this is the statement that the two projections onto the twice-occurring variables coincide.

For orientedness: an inverted pair $x, y$ excludes every common total order. Conversely, if there is no inverted pair, let $s = s_1 \cdots s_m$ be the common projection of $\alpha$ and $\beta$ onto the variables occurring on both sides. Each side is $s_1, \dots, s_m$ with blocks of once-occurring variables inserted in the gaps before $s_1$, between consecutive $s_i, s_{i+1}$, and after $s_m$. Order all variables by listing, gap by gap, first the once-occurring variables of $\alpha$ in that gap, then those of $\beta$, and then the next shared variable. Every side respects this total order, so the equation is oriented.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", 42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017), LIPIcs 83, Article 18, pp. 18:1–18:14, 2017, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Section 2 (regular, non-cross, quadratic and ordered equations; sides in $(\Sigma \cup X)^+$).
- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024, <https://doi.org/10.1007/s00224-021-10058-5>, Section 2 (quadratic, regular and regular-ordered equations via the projection onto twice-occurring variables; sides in $(X \cup \Sigma)^*$).
- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Section 2 (strictly regular-ordered equations and the examples above).
- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; read as the accepted version arXiv:2007.15478v6, Section 5.3 (regular and oriented equations).
