# Finiteness of the connected components of real algebraic varieties and groups

This node is still to be broken down. It covers the topological finiteness that the real case of linear
algebraic groups uses. Real points carry the topology induced by that of $\mathbb{R}$.

- **Real algebraic varieties** (Whitney). For an algebraic [variety](../../AlgebraicGeometry/schemes-and-morphisms/varieties-over-a-field/is-variety.md) $X$ over $\mathbb{R}$, the
  space $X(\mathbb{R})$ has finitely many path components and topological dimension at most $\dim X$. If $X$ is
  nonsingular, $X(\mathbb{R})$ is a real analytic manifold whose dimension at each point $x$ is the local dimension
  $\dim_x X$; it is $\dim X$ everywhere when $X$ has pure dimension, but not in general, as the line $\mathbb{A}^1_{\mathbb{R}}$
  together with an isolated point $\operatorname{Spec} \mathbb{R}$ shows.
- **Real algebraic groups** (Matsumoto). Let $G$ be a connected linear algebraic group over $\mathbb{R}$ and $S$ a
  maximal $\mathbb{R}$-split torus of $G$. Then $G(\mathbb{R}) = G(\mathbb{R})^0 \, S(\mathbb{R})$, where
  $G(\mathbb{R})^0$ is the identity component. In particular $G(\mathbb{R})/G(\mathbb{R})^0$ is a quotient of
  $S(\mathbb{R})/S(\mathbb{R})^0 \cong (\mathbb{Z}/2\mathbb{Z})^{\dim S}$.

## Expansion

A good expansion has statement pages for Whitney's theorem and for Matsumoto's theorem, each citing the
sources below with locators. Borel and Tits prove the second (14.4) by reduction to reductive $G$, through
a minimal parabolic $\mathbb{R}$-subgroup $P$ containing $S$, the connectedness of $(G/P)(\mathbb{R})$ (14.2) and the
exact homotopy sequence.

## Depends on

- [Geometrically reduced variety over a field](../../AlgebraicGeometry/schemes-and-morphisms/varieties-over-a-field/is-variety.md), for varieties over $\mathbb{R}$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: §14, 14.1 (for an $\mathbb{R}$-variety $X$, $X_{\mathbb{R}}$ has
  finitely many path components, of topological dimension at most $\dim X$ and analytic of dimension $\dim X$ for
  nonsingular $X$, which needs $X$ of pure dimension, citing Whitney as [40]), 14.2 (for $P$ a parabolic $\mathbb{R}$-subgroup of a connected $G$, $(G/P)_{\mathbb{R}}$ is
  a compact connected manifold) and 14.4 (Matsumoto: $G_{\mathbb{R}} = (G_{\mathbb{R}})^0 \cdot S_{\mathbb{R}}$), pp. 145–146.
- H. Whitney, "Elementary structure of real algebraic varieties", Ann. of Math. (2) 66 (1957), 545–556, the
  original theorem, as cited by Borel and Tits.
