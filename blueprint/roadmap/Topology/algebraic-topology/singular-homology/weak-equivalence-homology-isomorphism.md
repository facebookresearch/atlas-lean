# A weak homotopy equivalence induces isomorphisms on singular homology with any coefficients

Let $f\colon X \to Y$ be a weak homotopy equivalence of topological spaces. This means that $f$ induces a bijection on path components and, for every $x_0 \in X$ and every $n \ge 1$, an isomorphism $f_*\colon \pi_n(X, x_0) \to \pi_n(Y, f(x_0))$. Then for every abelian group $G$ and every integer $n \ge 0$, the induced homomorphism $f_*\colon H_n(X; G) \to H_n(Y; G)$ on singular homology with coefficients in $G$ is an isomorphism.

## Proof sketch

If $X$ is empty, so is $Y$, because $f$ is bijective on path components, and there is nothing to prove; so let $X$ be nonempty. Let $i\colon X \to M_f$ include $X$ into the mapping cylinder, with retraction $r\colon M_f \to Y$ satisfying $r \circ i = f$. Since $M_f$ deformation retracts onto $Y$, $r$ is a homotopy equivalence; it induces isomorphisms on homotopy groups and, by homotopy invariance of singular homology with coefficients in $G$, on $H_n(\,\cdot\,; G)$. As $r \circ i = f$, the map $i$ is a weak homotopy equivalence too, and it suffices to show that $i_*$ is an isomorphism on $H_n(\,\cdot\,; G)$. The map $\pi_0(X) \to \pi_0(M_f)$ is bijective, and the long exact homotopy sequence of $(M_f, X, x_0)$ shows that $\pi_i(M_f, X, x_0)$ is trivial for every $i \ge 1$ and every $x_0 \in X$. It suffices to prove that $H_k(M_f, X; G) = 0$ for every $k \ge 0$, and then to apply the long exact sequence of the pair $(M_f, X)$ with coefficients in $G$ in degrees $n + 1$ and $n$: in its segment $H_{n+1}(M_f, X; G) \to H_n(X; G) \to H_n(M_f; G) \to H_n(M_f, X; G)$, vanishing in degree $n + 1$ makes $i_*$ injective and vanishing in degree $n$ makes it surjective. Each class in $H_k(M_f, X; G)$ is the image of a class under a map of pairs $(K, L) \to (M_f, X)$, with $K$ a finite $\Delta$-complex and $L$ a subcomplex. Since every path component of $M_f$ meets $X$ and the relative homotopy sets $\pi_i(M_f, X, x_0)$, $i \ge 1$, are trivial at every basepoint $x_0 \in X$, the compression lemma, applied to the finite CW pair $(K, L)$, deforms this map rel $L$, through maps of pairs, to a map into $X$. By homotopy invariance and functoriality of relative homology the class therefore factors through $H_k(X, X; G) = 0$, so it is zero.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the long exact sequence of a pair in homology with coefficients; the compression lemma; the isomorphisms induced on homotopy groups by homotopy equivalences; the deformation retraction of a mapping cylinder onto its target; the representation of relative homology classes by finite Δ-complex pairs; the homotopy invariance of relative homology with coefficients; the functoriality of the homomorphisms induced on relative homology; singular homology with coefficients; weak homotopy equivalences.

## Proof depends on

- [Long exact sequence of homotopy groups of a pair](../higher-homotopy-groups/homotopy-les-pair.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Proposition 4.21.
