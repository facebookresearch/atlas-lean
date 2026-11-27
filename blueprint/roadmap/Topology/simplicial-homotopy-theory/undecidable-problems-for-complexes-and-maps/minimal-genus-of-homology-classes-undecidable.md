# The minimal genus of a homology class in a finite 2-complex is not computable

There is no algorithm that decides, for a finite $2$-complex $X$, a class $\omega \in H_2(X; \mathbb{Z})$ and a bound $B$, whether $\omega$ is represented by a map of a closed oriented surface of total genus at most $B$; the same holds for the complexity $\chi^-$.

Let $X$ be a CW complex and $\omega \in H_2(X; \mathbb{Z})$. A *surface representative* of $\omega$ is a continuous map $f : \Sigma \to X$, not necessarily an embedding, of a closed oriented, possibly disconnected, surface $\Sigma$ with $f_*[\Sigma] = \omega$. With sums over the connected components $\Sigma'$ of $\Sigma$, set

$$
g(\Sigma) = \sum_{\Sigma'} g(\Sigma'), \qquad \chi^-(\Sigma) = \sum_{\Sigma'} \max\{0, -\chi(\Sigma')\},
$$

and let $g(\omega)$ and $\chi^-(\omega)$ be the minima of these invariants over all surface representatives of $\omega$.

**Theorem (Kastenholz–Pedron).** Let $B$ be a positive integer and let $i$ be either $\chi^-$ or $g$. There is no algorithm that takes as input (an encoding of) a finite $2$-complex $X$ and a homology class $\omega \in H_2(X; \mathbb{Z})$, and outputs whether $i(\omega) \le B$.

Conventions: $B$ is fixed and the complex and class are the input; for each fixed $B$ the problem is undecidable, so in particular $g$ and $\chi^-$ are not computable functions of $(X, \omega)$. For a connected surface that is not a sphere, $\chi^- = 2g - 2$, but for disconnected surfaces the two minimization problems can differ. In contrast, the source gives an algorithm computing both invariants for a class of complexes that includes all $2$-dimensional CAT($-1$) complexes.

## Depends on

- [Integral singular homology](../../algebraic-topology/hurewicz-theorem/integral-homology.md)
- [R-orientation of a topological manifold](../../algebraic-topology/homological-orientation.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The reduction is from the word problem for finitely presented groups, via a construction of Gordon (C. McA. Gordon, "Some embedding theorems and undecidability questions for groups", in *Combinatorial and Geometric Group Theory (Edinburgh, 1993)*, London Mathematical Society Lecture Note Series 204, Cambridge University Press, 1995, pp. 105–110, as stated in the source). Given a finite presentation $\Pi$ and a word $w$, one adds generators $a, \alpha, b, \beta$ and $m + 4$ relations, $m$ being the number of generators of $\Pi$, to obtain a presentation $\Pi_w$ of a group that is trivial if $w = 1$ in the group of $\Pi$, while $a$ and $b$ have infinite order otherwise; in both cases $a$ and $b$ are explicit commutators. The complex $X_{\Pi, w}$ is the presentation complex of $\Pi_w$ with a cell of type $\Sigma_{B,2}$, a surface of genus $B$ with two boundary circles, glued along $a$ and $b$, and $\omega_{\Pi, w}$ is the fundamental class of that cell plus the classes of the two commutators. Then $\omega_{\Pi,w}$ has a representative of genus at most $B$ exactly when $w$ is trivial, so an algorithm for the problem would solve the word problem. Minimizing representatives here are essentially connected, which transfers the conclusion from $g$ to $\chi^-$.

## Sources

- Thorben Kastenholz and Mark Pedron, *The minimal genus of homology classes in a finite 2-complex*, Algebr. Geom. Topol. 22 (2022), no. 3, 1375–1415, https://doi.org/10.2140/agt.2022.22.1375, read in the copy arXiv:2002.08485v1, whose numbering is used here: the statement is Theorem A ("Minimal Genus is Undecidable") in its introduction, with the definitions of $g$ and $\chi^-$ at the start of the introduction, Gordon's construction and the proof of Theorem A in its section on undecidability.
