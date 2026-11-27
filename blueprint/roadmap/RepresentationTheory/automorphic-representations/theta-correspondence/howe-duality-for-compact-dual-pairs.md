# Duality for compact dual pairs in the Fock model

Let $(L, \mathfrak{l}')$ be a dual pair in $\mathfrak{sp}_{2N}(\mathbb{R})$ with $L$ compact and contained in the
maximal compact subgroup $\mathrm{U}(N)$ of $\mathrm{Sp}_{2N}(\mathbb{R})$, $\tilde L$ and $\tilde{\mathrm U}(N)$ the
inverse images of $L$ and $\mathrm{U}(N)$ in the twofold cover of $\mathrm{Sp}_{2N}(\mathbb{R})$, and $\mathcal{P}$ the
space of polynomials on $\mathbb{C}^N$ of the Fock model of the
[oscillator representation](metaplectic-group-and-local-weil-representation.md). In the Fock model
$\omega(\mathfrak{sp}_{\mathbb{C}}) = \mathfrak{sp}^{(1,1)} \oplus \mathfrak{sp}^{(2,0)} \oplus \mathfrak{sp}^{(0,2)}$, where
$\mathfrak{sp}^{(1,1)}$ is spanned by the operators $\tfrac12(z_i \partial_j + \partial_j z_i) = z_i \partial_j + \tfrac12 \delta_{ij}$,
$\mathfrak{sp}^{(2,0)}$ by the multiplications $z_i z_j$ and $\mathfrak{sp}^{(0,2)}$ by the operators $\partial_i \partial_j$.
Thus $\tilde{\mathrm U}(N)$ acts on the polynomials of degree $d$ by the natural action twisted by a genuine
square root of $\det$: a lift of the rotation by $2\pi$ in a coordinate circle acts by $-1$. Let
$\mathfrak{l}'_{\mathbb{C}} = \mathfrak{l}'^{(1,1)} \oplus \mathfrak{l}'^{(2,0)} \oplus \mathfrak{l}'^{(0,2)}$ be the intersections with the
three summands, $\mathcal{P} = \bigoplus_\sigma \mathcal{P}_\sigma$ the isotypic decomposition under $\tilde L$, the
$\sigma$ running over the set $\mathcal{R}(\tilde L, \omega)$ of irreducible representations of $\tilde L$ occurring in
$\mathcal{P}$ (genuine representations of $\tilde L$), and $\mathcal{H}(L)$ the polynomials killed by $\mathfrak{l}'^{(0,2)}$
(the $L$-harmonics), with $\mathcal{H}(L)_\sigma = \mathcal{H}(L) \cap \mathcal{P}_\sigma$.

1. $\tilde L \times \mathfrak{l}'$ acts irreducibly on each $\mathcal{P}_\sigma$.
2. $\mathcal{H}(L)_\sigma$ is the space of polynomials of lowest degree in $\mathcal{P}_\sigma$.
3. $\mathcal{P}_\sigma = \mathcal{U}(\mathfrak{l}'^{(2,0)}) \cdot \mathcal{H}(L)_\sigma$.
4. Each $\mathcal{H}(L)_\sigma$ is irreducible under $\tilde L \times \mathfrak{l}'^{(1,1)}$, of the form $\sigma \otimes \tau'$, and
   $\sigma$ determines $\tau'$ and conversely, so that $\sigma \mapsto \tau'$ is injective.

**Products of unitary groups.** For $L = \mathrm{U}(n)$ acting on $\mathbb{C}^n \otimes \mathbb{C}^m$ ($N = nm$), the
compact pair is $(\mathrm{U}(n), \mathrm{U}(m))$, and $\mathfrak{l}'^{(1,1)}$ is the complexified Lie algebra $\mathfrak{gl}_m$ of
$\mathrm{U}(m)$. Up to the genuine determinant twists above, the joint action of $\tilde{\mathrm U}(n) \times \tilde{\mathrm U}(m)$
on $\mathcal{P} = S(\mathbb{C}^n \otimes \mathbb{C}^m)$ is the restriction of the polynomial action of
$\mathrm{GL}_n(\mathbb{C}) \times \mathrm{GL}_m(\mathbb{C})$, decomposed by the
[$(\mathrm{GL}_m, \mathrm{GL}_n)$ duality on symmetric algebras](../../lie-and-topological-representations/schur-weyl-duality/gl-m-gl-n-howe-duality.md):
each isotypic component of $\mathcal{P}$ under $\tilde{\mathrm U}(n)$ is an irreducible
$\tilde{\mathrm U}(n) \times \tilde{\mathrm U}(m)$-module, and the occurring types of the two factors, attached to Young
diagrams with at most $\min(n, m)$ rows, are matched one to one.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the twofold cover, the Fock model of the oscillator representation and the decomposition of $\mathfrak{sp}_{\mathbb{C}}$
- [$(\mathrm{GL}_m, \mathrm{GL}_n)$ duality on symmetric algebras of tensor products](../../lie-and-topological-representations/schur-weyl-duality/gl-m-gl-n-howe-duality.md), for the decomposition of the polynomial action used in the case of products of unitary groups

## Proof depends on

- [Classical invariant theory and harmonics](classical-invariant-theory-and-harmonics.md), for the theorems of Howe on invariants and harmonics of the classical groups from which items 1–4 follow
- [$(\mathrm{GL}_m, \mathrm{GL}_n)$ duality on symmetric algebras of tensor products](../../lie-and-topological-representations/schur-weyl-duality/gl-m-gl-n-howe-duality.md), for the case of products of unitary groups

## Sources

- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §2, (2.1)–(2.3) (the Fock model and the operators
  spanning $\mathfrak{sp}^{(1,1)}$, $\mathfrak{sp}^{(2,0)}$, $\mathfrak{sp}^{(0,2)}$); §3, (3.6)–(3.9) (the compact case, "from
  Classical Invariant Theory ... as explained in [H1]"; (3.9)(d) in its "equivalently" form, item 4; the
  covering groups are not distinguished in the notation there) and (3.11)–(3.13) (the pair of products of
  unitary groups).
- R. Howe, "Remarks on classical invariant theory", Trans. Amer. Math. Soc. 313 (1989), 539–570,
  <https://doi.org/10.1090/S0002-9947-1989-0986027-X>: Theorems 7–9 (the classical invariant theory behind
  (3.9)), and §4 (d) (the decomposition of $S(V \otimes D)$ under $\mathrm{GL}(V) \times \mathrm{GL}(D)$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the ordinary polynomial $(\mathrm{GL}_n(\mathbb{C}), \mathrm{GL}_m(\mathbb{C}))$ decomposition and its restriction
  to $\mathrm{U}(n) \times \mathrm{U}(m)$, for positive ranks, as `GlobalTheory.Published.GLHoweDuality`.
