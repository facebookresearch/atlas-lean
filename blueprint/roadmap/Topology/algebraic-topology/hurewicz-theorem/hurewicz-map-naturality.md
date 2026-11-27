# Naturality of the Hurewicz maps

For each $n \ge 1$, let $c_n\colon (D^n, S^{n-1}) \to (S^n, s_0)$ be the map fixed in the definition of $j_*$ in the long exact sequence of homotopy groups of a pair, the same for every pair: it sends $S^{n-1}$ to $s_0$ and induces a homeomorphism $D^n/S^{n-1} \cong S^n$. Let $\iota_n\colon H_n(S^n) \to H_n(S^n, \{s_0\})$ be the canonical map, an isomorphism for $n \ge 1$. Fix generators $\alpha_n$ of $H_n(S^n) \cong \mathbb{Z}$ and $\beta_n$ of $H_n(D^n, S^{n-1}) \cong \mathbb{Z}$, chosen compatibly with $c_n$: $(c_n)_*(\beta_n) = \iota_n(\alpha_n)$ in $H_n(S^n, \{s_0\})$, and $\partial \beta_n = \alpha_{n-1}$ for $n \ge 2$, where $\partial$ is the connecting homomorphism of the pair $(D^n, S^{n-1})$. Such choices exist. Let $h$ denote both the Hurewicz maps $\pi_n(X, x_0) \to H_n(X)$, $[f] \mapsto f_*(\alpha_n)$, and the relative Hurewicz maps $\pi_n(X, A, x_0) \to H_n(X, A)$, $[f] \mapsto f_*(\beta_n)$. Then:

1. For a based map $g\colon (X, x_0) \to (Y, y_0)$ and $n \ge 1$, $h \circ g_* = g_* \circ h$ as maps $\pi_n(X, x_0) \to H_n(Y)$. Likewise, for a map of pairs $g\colon (X, A) \to (Y, B)$ with $x_0 \in A$ and $g(x_0) = y_0$, $h \circ g_* = g_* \circ h$ as maps $\pi_n(X, A, x_0) \to H_n(Y, B)$.
2. For a pair $(X, A)$ with $x_0 \in A$, the Hurewicz maps commute with the maps of the long exact sequence of homotopy groups of $(X, A, x_0)$ and of the long exact sequence in singular homology of $(X, A)$. That is, $h \circ j_* = j_* \circ h$ on $\pi_n(X, x_0)$ for $n \ge 1$, and $h \circ \partial = \partial \circ h$ on $\pi_n(X, A, x_0)$ for $n \ge 2$.

## Proof sketch

For a based map, $h(g_*[f]) = (g \circ f)_*(\alpha_n) = g_* f_*(\alpha_n)$ by functoriality of singular homology. For a map of pairs, $g_*$ on $\pi_n(X, A, x_0)$ is postcomposition, and the same computation uses functoriality of relative homology. Since $j_*[f]$ is represented by $f \circ c_n$, with the same map $c_n$ that defines $j_*$, functoriality gives $h(j_*[f]) = f_* (c_n)_*(\beta_n) = f_* \iota_n(\alpha_n) = j_* f_*(\alpha_n)$, the last step by naturality of the maps $H_n(Y) \to H_n(Y, B)$. This is why the generators are tied to $c_n$: composing $c_n$ with a reflection of degree $-1$ changes $j_*$ on homotopy but not on homology, and the square for $j_*$ would then commute only up to sign. For $n \ge 2$, naturality of the connecting homomorphism, applied to the map of pairs $f\colon (D^n, S^{n-1}) \to (X, A)$, gives $\partial f_*(\beta_n) = (f|_{S^{n-1}})_*(\partial \beta_n) = (f|_{S^{n-1}})_*(\alpha_{n-1}) = h(\partial [f])$. The generators are chosen inductively. Each $H_n(D^n, S^{n-1})$ is infinite cyclic, and $(c_n)_*\colon H_n(D^n, S^{n-1}) \to H_n(S^n, \{s_0\})$ is an isomorphism by the good-pair isomorphism, since $c_n$ induces a homeomorphism $D^n/S^{n-1} \cong S^n$. Choose $\beta_1$ and put $\alpha_1 = \iota_1^{-1}(c_1)_*(\beta_1)$. For $n \ge 2$, $D^n$ is contractible, so by homotopy invariance it has the homology of a point, and the long exact sequence of $(D^n, S^{n-1})$ makes $\partial\colon H_n(D^n, S^{n-1}) \to H_{n-1}(S^{n-1})$ an isomorphism; let $\beta_n$ be the generator with $\partial \beta_n = \alpha_{n-1}$, and put $\alpha_n = \iota_n^{-1}(c_n)_*(\beta_n)$. For $n = 1$ the connecting map sends $H_1(D^1, S^0) \cong \mathbb{Z}$ isomorphically onto the reduced group $\tilde H_0(S^0) \cong \mathbb{Z}$, not onto $H_0(S^0) \cong \mathbb{Z}^2$, which is why the boundary clause is stated only for $n \ge 2$.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the homotopy invariance of singular homology; the naturality of the long exact sequence of a pair; the homology of a point; the functoriality of the homomorphisms induced on relative homology; the homology of a disc relative to its boundary sphere; the homology of spheres; homotopy groups; the homomorphisms induced on homotopy groups by based maps; the Hurewicz map; the homomorphisms induced on relative homology by maps of pairs; the maps induced on relative homotopy groups by maps of pairs; the homomorphisms induced on singular homology by continuous maps.

## Depends on

- [Integral singular homology](integral-homology.md)
- [Long exact sequence of a pair in singular homology](../singular-homology/homology-long-exact-sequence-pair.md)
- [Long exact sequence of homotopy groups of a pair](../higher-homotopy-groups/homotopy-les-pair.md)
- [Relative singular homology of a pair of spaces](../singular-homology/relative-homology.md)
- [Relative homotopy groups of a pair of spaces](../higher-homotopy-groups/relative-homotopy-group.md)
- [Relative Hurewicz map](relative-hurewicz-map.md)

## Proof depends on

- [The homology of a good pair is the reduced homology of its quotient](../singular-homology/good-pair-quotient-homology.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 4.2.
