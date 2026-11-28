# Continuous cohomology

Let $k$ be a ring with a topology and $G$ a topological group. A topological representation $X$ of $G$ over $k$
(Mathlib's `TopRep k G`) is a topological $k$-module on which $G$ acts by continuous $k$-linear maps. Its
resolution is the complex of topological representations

$$
X \to C(G, X) \to C(G, C(G, X)) \to \cdots,
$$

whose term in degree $n$ is the $n$-fold iterate of Mathlib's coinduction `TopRep.coind₁`, $X \mapsto C(G, X)$,
with differentials defined inductively by $d_0 \colon m \mapsto (g \mapsto m)$ and
$d_{n+1}(f) = (g \mapsto f - d_n(f(g)))$. The homogeneous cochain complex `TopRep.homogeneousCochains X` is the
complex of $G$-invariants of this resolution with its first term removed, a cochain complex of topological
$k$-modules, and the $n$-th continuous cohomology of $X$ is its $n$-th homology:

$$
\texttt{continuousCohomology}\ n\ X = H^n\bigl(\texttt{TopRep.homogeneousCochains}\ X\bigr),
$$

a topological $k$-module. Its degree-$0$ group is identified with the invariants $X^G$ by
`ContinuousCohomology.zeroIso`, and a continuous homomorphism $\varphi \colon H \to G$ with a morphism of
representations from the restriction of $X$ to $Y$ induces `ContinuousCohomology.map`. For a profinite group $G$
and a topological $G$-module $A$ (over $k = \mathbb{Z}$, or $k = \mathbb{Z}_\ell$), this is the continuous cochain
cohomology $H^n_{\mathrm{cts}}(G, A)$ of Neukirch–Schmidt–Wingberg (2.7.1), its cochains written in curried form.

## Sources

- Mathlib, `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` (`continuousCohomology`,
  `TopRep.homogeneousCochains`), `LowDegree.lean` (`ContinuousCohomology.zeroIso`) and `Functoriality.lean`
  (`ContinuousCohomology.map`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Definition (2.7.1) and the
  remark after it, pp. 136–137.
