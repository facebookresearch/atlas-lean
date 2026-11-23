# Duality for compact dual pairs and the (GLₙ, GLₘ)-duality

**$(\mathrm{GL}_n, \mathrm{GL}_m)$-duality.** Let $V$ and $D$ be complex vector spaces of dimensions $n$
and $m$, and let $\mathrm{GL}(V) \times \mathrm{GL}(D)$ act on the symmetric algebra
$S(V \otimes D)$, the polynomial functions on $V^* \otimes D^* \cong \mathrm{M}_{n \times m}(\mathbb{C})$.
Then $S(V \otimes D)$ is a direct sum of irreducible $\mathrm{GL}(V) \times \mathrm{GL}(D)$-modules, each
occurring once; the irreducible representations of $\mathrm{GL}(V)$ and of $\mathrm{GL}(D)$ that occur
are those whose Young diagrams have at most $\min(n, m)$ rows, and each summand is $\sigma \otimes \tau$
with $\sigma$ and $\tau$ attached to the same Young diagram. In particular the correspondence
$\sigma \leftrightarrow \tau$ between the representations that occur is a bijection.

**Compact dual pairs.** Let $(L, \mathfrak{l}')$ be a dual pair in $\mathfrak{sp}_{2N}(\mathbb{R})$ with $L$
compact and contained in the maximal compact subgroup $\mathrm{U}(N)$, and let $\mathcal{P}$ be the space
of polynomials of the Fock model of the
[oscillator representation](metaplectic-group-and-local-weil-representation.md), with the decomposition
$\mathfrak{l}'_{\mathbb{C}} = \mathfrak{l}'^{(1,1)} \oplus \mathfrak{l}'^{(2,0)} \oplus \mathfrak{l}'^{(0,2)}$
obtained by intersecting with the three summands of $\omega(\mathfrak{sp}_{\mathbb{C}})$. Write $\mathcal{P} = \bigoplus_\sigma \mathcal{P}_\sigma$
for the isotypic decomposition under $L$ and let $\mathcal{H}(L)$ be the polynomials killed by
$\mathfrak{l}'^{(0,2)}$ (the $L$-harmonics). Then:

1. $L \times \mathfrak{l}'$ acts irreducibly on each $\mathcal{P}_\sigma$;
2. $\mathcal{H}(L) \cap \mathcal{P}_\sigma$ is the space of polynomials of lowest degree in
   $\mathcal{P}_\sigma$;
3. $\mathcal{P}_\sigma = \mathcal{U}(\mathfrak{l}'^{(2,0)}) \cdot (\mathcal{H}(L) \cap \mathcal{P}_\sigma)$;
4. $L$ and $\mathfrak{l}'^{(1,1)}$ generate mutual commutants on $\mathcal{H}(L)$: each
   $\mathcal{H}(L) \cap \mathcal{P}_\sigma$ is an irreducible $L \times \mathfrak{l}'^{(1,1)}$-module
   $\sigma \otimes \tau'$, and $\sigma$ and $\tau'$ determine each other.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the Fock model of the oscillator representation and the decomposition of $\mathfrak{sp}_{\mathbb{C}}$

## Sources

- R. Howe, "Remarks on classical invariant theory", Trans. Amer. Math. Soc. 313 (1989), 539–570,
  <https://doi.org/10.1090/S0002-9947-1989-0986027-X>: §1 (the classical groups over $\mathbb{C}$),
  Theorem 8 (the joint action of $G$ and $\Gamma'$ on each isotypic component is irreducible, and the
  correspondence is a bijection) and §4 (d) (the decomposition of $S(V \otimes D)$, "each occurring
  once", with diagrams of at most $\min(\dim V, \dim D)$ rows matched when equal).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §3, (3.6)–(3.9) (the compact case, "from Classical
  Invariant Theory ... as explained in [H1]") and (3.11) (the pair of products of unitary groups).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the $(\mathrm{GL}_n(\mathbb{C}), \mathrm{GL}_m(\mathbb{C}))$ and $(\mathrm{U}(n), \mathrm{U}(m))$
  cases as `GlobalTheory.Published.GLHoweDuality`.
