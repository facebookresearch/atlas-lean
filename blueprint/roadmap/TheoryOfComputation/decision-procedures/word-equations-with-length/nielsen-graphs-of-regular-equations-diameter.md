# Nielsen graphs of regular equations have polynomial diameter

For a regular word equation $E$, any two equations of its Nielsen graph that are joined by a directed path are joined by one of length $O(|E|^{12})$. This polynomial bound is what places regular equations in NP.

Let $E$ be a regular word equation over an alphabet of constants with at least two letters, let $G_E$ be its Nielsen graph (the equations reachable from $E$ by the Nielsen transformation relation $\Rightarrow_{NT}$, with one labelled edge for each step; loops and parallel edges do not change shortest directed paths), and let $\mathrm{diam}(G_E)$ be the maximum, over ordered pairs of vertices $(E_1, E_2)$ such that $E_2$ is reachable from $E_1$, of the length of a shortest directed path from $E_1$ to $E_2$; pairs without a path are ignored, so a graph that is not strongly connected does not get infinite diameter. Then

$$\mathrm{diam}(G_E) \in O(|E|^{12}),$$

where the constant in the $O$ does not depend on $E$.

## Depends on

- [Nielsen transformations of quadratic word equations](nielsen-transformations.md)
- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)

## Proof depends on

None.

## Expansion

The source proves the bound from the following results of the same paper, stated here so that each step can be checked. Write $\Rightarrow$ for the length-preserving part of $\Rightarrow_{NT}$ and $G^{\Rightarrow}_{[E]}$ for the subgraph on the $\Rightarrow$-class of $E$; for regular equations $\Rightarrow^*$ is an equivalence relation.

1. *Components (Proposition 3.5).* $\mathrm{diam}(G_E) \le (|E| + 1)(1 + m) - 1$, where $m$ is the largest diameter of $G^{\Rightarrow}_{[E']}$ over equations $E'$ reachable from $E$: a path visits the length classes in decreasing order of length, at most $|E| + 1$ of them.
2. *Reduction to basic equations (Theorem 4.8).* An equation is *basic* if it is indecomposable (no proper nonempty prefixes $\alpha', \beta'$ of the two sides contain the same twice-occurring variables) and both sides consist of twice-occurring variables only. For a regular $E$ given by $\alpha = \beta$, let $\alpha', \beta'$ be the shortest nonempty prefixes of $\alpha, \beta$ such that $\mathrm{var}(\alpha') \cap \mathrm{qv}(E) = \mathrm{var}(\beta') \cap \mathrm{qv}(E)$, where $\mathrm{qv}(E)$ is the set of twice-occurring variables, and let $E'$ be the projection $\pi_{\mathrm{qv}(E)}(\alpha') = \pi_{\mathrm{qv}(E)}(\beta')$. Then $E'$ is basic and $G^{\Rightarrow}_{[E']}$ is isomorphic to an *isolated path compression of order $|E|$* of $G^{\Rightarrow}_{[E]}$: For the nondegenerate components, the original component is obtained from the basic one by replacing edges with isolated paths, so Remark 4.6 bounds its diameter by $|E|+1$ times the basic diameter. The zero- and one-variable cases must first be treated separately as in Lemma 4.7: an isolated cycle of linear length can project to the one-vertex basic component $x=x$ of diameter zero. Such a cycle uses its linear bound, not a multiple of zero. If a side of $E$ is empty, there is no nonempty prefix to take; then no step of $\Rightarrow$ applies and the component of $E$ is the single vertex $E$, of diameter $0$.
3. *Non-jumbled basic equations (Theorem 6.8).* For a basic $E$ and the set $\Delta(E)$ of variables determined by an invariant of $\Rightarrow$ (Theorem 5.3), the projection $E_Y$ onto $Y = \mathrm{var}(E) \setminus \Delta(E)$ is *jumbled* (Lemma 6.3) and $\mathrm{diam}(G^{\Rightarrow}_{[E]}) \in O(\max\{1, \mathrm{diam}(G^{\Rightarrow}_{[E_Y]})\} \cdot |E|^2)$.
4. *Jumbled basic equations (Theorems 7.11 and 8.10).* Every vertex of the component of a jumbled basic equation reaches, and is reached from, an equation in *Lex Normal Form* within $O(|E|^4)$ steps, and the component contains at most $|E|^4$ equations in Lex Normal Form. A pigeonhole argument on a shortest path then gives diameter $O(|E|^8)$.

Combining 4, 3, 2 and 1 gives $O(|E|^8)$ for jumbled components, $O(|E|^{10})$ for basic ones, $O(|E|^{11})$ for every component, and $O(|E|^{12})$ for $G_E$ (Theorem 8.11). The definitions of $\Delta(E)$, jumbled equations and Lex Normal Form are technical and are not reproduced here.

## Sources

- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024, <https://doi.org/10.1007/s00224-021-10058-5>, Section 2 (diameter convention, alphabet with at least two letters), Proposition 3.5, Definition 4.1 (basic equations), Definition 4.5 and Remark 4.6 (isolated path compression), Lemma 4.7 (including the zero- and one-variable cases), Theorem 4.8, Theorem 5.3, Lemma 6.3, Theorem 6.8, Theorem 7.11, Theorem 8.10 and Theorem 8.11 (the bound $O(|E|^{12})$, with its proof).
