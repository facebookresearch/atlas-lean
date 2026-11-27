# Directed figures and decipherable directed figure codes

A directed figure is a labeled polyomino with a start point and an end point; figures are catenated by gluing the start of one to
the end of the other, and a finite set of figures is a code of a given decipherability kind if equal catenations always come from
equal sequences, multisets, sets or numbers of figures.

**Directed figures.** Let $\Sigma$ be a finite nonempty alphabet. A *directed figure* over $\Sigma$ is a quadruple $f = (D, b, e, \ell)$ with a
finite nonempty domain $D \subseteq \mathbb{Z}^2$, a start point $b \in \mathbb{Z}^2$, an end point $e \in \mathbb{Z}^2$ and a labeling
$\ell : D \to \Sigma$; the start and end points need not lie in $D$. Its *translation vector* is $e - b$. The *empty figure* is
$\varepsilon = (\emptyset, (0, 0), (0, 0), \{\})$. Figures are considered up to translation: $x$ and $y$ are equal if translating all
components of $x$ by some $u \in \mathbb{Z}^2$ gives $y$.

**Catenation.** For figures $x = (D_x, b_x, e_x, \ell_x)$ and $y = (D_y, b_y, e_y, \ell_y)$, let $y'$ be $y$ translated by $e_x - b_y$, so
that its start point is $e_x$. If $D_x$ and the domain of $y'$ are disjoint, the *catenation* $x \circ y$ is the figure with domain
$D_x \cup D_{y'}$, start point $b_x$, end point the end point of $y'$, and the labels of $x$ and $y'$; if the domains overlap, $x \circ y$
is undefined. (A variant, $m$-catenation, resolves overlaps with a merging function.)

**Codes.** A *code* is a finite nonempty set $X$ of nonempty directed figures. For $x_1, \dots, x_k, y_1, \dots, y_l \in X$ such that
$x_1 \circ \cdots \circ x_k = y_1 \circ \cdots \circ y_l$ (both defined), $X$ is

- *uniquely decipherable* (UD) if this always forces $k = l$ and $x_i = y_i$ for all $i$;
- *multiset decipherable* (MSD) if it always forces equality of the multisets $\{\{x_1, \dots, x_k\}\}$ and $\{\{y_1, \dots, y_l\}\}$;
- *set decipherable* (SD) if it always forces $\{x_1, \dots, x_k\} = \{y_1, \dots, y_l\}$;
- *numerically decipherable* (ND) if it always forces $k = l$.

A code $X = \{x_1, \dots, x_n\}$ is *two-sided* if some nonnegative integers $\alpha_1, \dots, \alpha_n$, not all zero, satisfy
$\sum_i \alpha_i (e_{x_i} - b_{x_i}) = (0, 0)$, that is, if the translation vectors do not fit in an open half-plane; otherwise it is
*one-sided*. Words are the special case of figures on a horizontal line with translation vector $(1, 0)$ per letter.

## Depends on

None.

## Proof depends on

None.

## Sources

- W. Moczurad, "Decidability of multiset, set and numerically decipherable directed figure codes", *Discrete Mathematics and Theoretical Computer Science* 19(1), paper 11, 2017, doi:10.23638/DMTCS-19-1-11; read in arXiv:1604.02167v3: Section 2, Definitions 1 (directed figure) and 2 (catenation), Section 3, Definitions 4 to 8 (UD, MSD, SD and ND codes and $m$-codes) and Definition 9 (two-sided and one-sided codes).
