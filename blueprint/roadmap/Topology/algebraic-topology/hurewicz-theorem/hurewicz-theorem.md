# Hurewicz theorem for (n−1)-connected spaces, n ≥ 2

Let $n \ge 2$ and let $X$ be an $(n-1)$-connected space: $X$ is nonempty and path-connected, and $\pi_i(X, x_0) = 0$ for $1 \le i \le n-1$ and every $x_0 \in X$. Then the reduced singular homology groups satisfy $\tilde H_i(X) = 0$ for all $i < n$. Moreover, for every $x_0 \in X$ the Hurewicz map $h\colon \pi_n(X, x_0) \to H_n(X)$ is a group isomorphism. This map sends the class of a based map $f\colon (S^n, s_0) \to (X, x_0)$ to $f_*(\alpha)$, for a fixed generator $\alpha$ of $H_n(S^n) \cong \mathbb{Z}$.

## Proof sketch

Replacing $\alpha$ by $-\alpha$ replaces $h$ by $-h$, so the conclusions do not depend on the choice of $\alpha$. Take $\alpha = \alpha_n$, where the generators $\alpha_k$ of $H_k(S^k)$ and $\beta_k$ of $H_k(D^k, S^{k-1})$, $k \ge 1$, are chosen compatibly with the maps $c_k$ that define $j_*$, as in the naturality of the Hurewicz maps, and use them for all absolute and relative Hurewicz maps below; with these choices the squares used below commute exactly. By CW approximation, the fact that weak homotopy equivalences induce isomorphisms on integral homology, and naturality of the Hurewicz maps, we may take $X$ to be a CW complex, and by the cell reduction for $(n-1)$-connected CW complexes one whose $(n-1)$-skeleton is the basepoint. Cellular homology gives $\tilde H_i(X) = 0$ for $i < n$. The pair $(X, X^{n+1})$ is $(n+1)$-connected, as all its cells have dimension at least $n + 2$ (cellular approximation), so $X^{n+1} \hookrightarrow X$ is bijective on $\pi_n$; it is bijective on $H_n$ because cellular homology in degree $n$ only involves cells of dimension at most $n + 1$. So take $X = X^{n+1}$. Then $X^n$ is a wedge of $n$-spheres and $X/X^n$ a wedge of $(n+1)$-spheres. The pair $(X, X^n)$ is $n$-connected and $H_n(X, X^n) = 0$, so the long exact sequences of the pair give exact rows $\pi_{n+1}(X, X^n) \to \pi_n(X^n) \to \pi_n(X) \to 0$ and $H_{n+1}(X, X^n) \to H_n(X^n) \to H_n(X) \to 0$. The relative and absolute Hurewicz maps form the vertical maps, and the squares commute by naturality. The vertical map at $\pi_n(X^n)$ is an isomorphism: for $n \ge 2$, $\pi_n$ of a wedge of $n$-spheres is free abelian on the classes of the summand inclusions, $H_n$ of the wedge is free abelian on the images of the fundamental classes of the summands (homology of spheres and of wedge sums), and the Hurewicz homomorphism sends each inclusion class to the corresponding image. At $\pi_{n+1}(X, X^n)$: since $(X, X^n)$ is $n$-connected and $X^n$ is $(n-1)$-connected, the quotient comparison for CW pairs makes $\pi_{n+1}(X, X^n) \to \pi_{n+1}(X/X^n)$ an isomorphism, as $n + 1 \le 2n - 1$ for $n \ge 2$. Also $H_{n+1}(X, X^n) \to \tilde H_{n+1}(X/X^n)$ is an isomorphism, because a CW pair with nonempty subcomplex is a good pair. By naturality under the quotient map, the relative Hurewicz map there is identified with the absolute Hurewicz map of the wedge $X/X^n$ of $(n+1)$-spheres, which is a homomorphism and an isomorphism by the same argument in degree $n + 1$. Appending zeros to both rows, the five lemma shows that the Hurewicz map $\pi_n(X) \to H_n(X)$ is an isomorphism.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the cellular approximation theorem; the isomorphism between cellular and singular homology; the reduction of an (n−1)-connected CW complex to one whose (n−1)-skeleton is a point; CW approximation; the fact that a CW pair with a nonempty subcomplex is a good pair; the connectivity of a CW pair whose relative cells all have high dimension; the quotient of consecutive skeleta of a CW complex as a wedge of spheres; the five lemma; the homology of spheres; the fact that the Hurewicz map is a homomorphism; the n-th homotopy group of a wedge of n-spheres; the reduced homology of a wedge sum; the functoriality of the homomorphisms induced on relative homology; the maps induced on relative homotopy groups by maps of pairs; the Hurewicz map; n-connected spaces; reduced singular homology.

## Proof depends on

- [Homotopy groups of a connected CW pair and of its quotient](../higher-homotopy-groups/cw-pair-quotient-homotopy-isomorphism.md)
- [The homology of a good pair is the reduced homology of its quotient](../singular-homology/good-pair-quotient-homology.md)
- [Long exact sequence of a pair in singular homology](../singular-homology/homology-long-exact-sequence-pair.md)
- [Long exact sequence of homotopy groups of a pair](../higher-homotopy-groups/homotopy-les-pair.md)
- [Naturality of the Hurewicz maps](hurewicz-map-naturality.md)
- [Relative Hurewicz map](relative-hurewicz-map.md)
- [A weak homotopy equivalence induces isomorphisms on singular homology with any coefficients](../singular-homology/weak-equivalence-homology-isomorphism.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Theorems 4.32 and 4.37.
