# Cartan decomposition and Satake isomorphism for special maximal compact subgroups

This node is still to be broken down. It covers the Cartan decomposition and the Satake isomorphism that the
pages on asymptotics of matrix coefficients, on the unramified theta correspondence and on base change use.
Let $F$ be a non-archimedean local field, $\mathbf{G}$ a connected reductive group over $F$, $A$ a maximal $F$-split
torus, $M = \mathrm{Cent}_{\mathbf{G}}(A)$, $W = W(\mathbf{G}, A)$ the relative Weyl group, $v$ a special vertex of
the Bruhat–Tits building in the apartment of $A$, and $\tilde K$ the special maximal compact open subgroup fixing
$v$. Let $M(F)^1$ be the maximal compact open subgroup of $M(F)$ and $\tilde\Lambda_M = M(F)/M(F)^1$, a free abelian
group containing $X_*(A)$ with the same rank.

- **Cartan decomposition** (Cartier). $\tilde K \backslash G(F) / \tilde K \cong W \backslash \tilde\Lambda_M$; for
  $\mathbf{G}$ unramified, $\tilde\Lambda_M = X_*(A)$ and $\tilde K \backslash G(F) / \tilde K \cong W \backslash X_*(A)$.
- **Satake isomorphism** (Satake, Cartier). The Hecke algebra $\mathcal{H}_{\tilde K} = C_c^\infty(\tilde K \backslash
  G(F) / \tilde K)$, under convolution for the Haar measure giving $\tilde K$ volume $1$, is isomorphic, as a
  $\mathbb{C}$-algebra, to $\mathbb{C}[\tilde\Lambda_M]^W$; for $\mathbf{G}$ unramified, to $\mathbb{C}[X_*(A)]^W$. The isomorphism is the Satake transform $f \mapsto \big(m \mapsto \delta_P(m)^{1/2} \int_{N(F)} f(mn) \, dn\big)$
  for a minimal parabolic subgroup $P = MN$, with modulus character $\delta_P$ and the Haar measure $dn$ on $N(F)$ giving
  $N(F) \cap \tilde K$ volume $1$; with another normalization of $dn$ the transform sends the unit $1_{\tilde K}$ of $\mathcal{H}_{\tilde K}$ to
  $\mathrm{vol}(N(F) \cap \tilde K)$ times the unit.
- **Parahoric form** (Haines–Rostami). For the special maximal parahoric subgroup $K \subseteq \tilde K$ attached to
  $v$ and $\Lambda_M = M(F)/M(F)_1$, with $M(F)_1$ the parahoric subgroup of $M(F)$, there is a canonical isomorphism
  $\mathcal{H}_K \cong \mathbb{C}[\Lambda_M]^W$; $\tilde\Lambda_M = \Lambda_M/\text{torsion}$, and $K = \tilde K$ when $\mathbf{G}$
  is unramified or semisimple and simply connected.

## Expansion

A good expansion has statement pages for the Cartan decomposition and for the Satake isomorphism, first for
unramified groups and hyperspecial subgroups, then for special maximal compact and special maximal parahoric
subgroups, each citing the sources below with locators. The unramified Satake parameters of an unramified
representation are read off from the character of $\mathbb{C}[X_*(A)]^W$ by which $\mathcal{H}_{\tilde K}$ acts on its
$\tilde K$-fixed line.

## Depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the building, special vertices and
  the maximal split torus
- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the setting
- [Hecke-algebra corners of smooth representations and independence of their characters](hecke-algebra-corners-and-character-independence.md), for the algebra of bi-invariant locally constant compactly supported functions under convolution, with its normalized idempotent
- [Haar measure](../../../MeasureTheory/haar-measure/is-haar-measure.md), for the Haar measure of $G(F)$ normalized by the volume of $\tilde K$

## Proof depends on

- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the relative Weyl
  group
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for minimal parabolic
  subgroups and their modulus characters, used in the Satake transform

## Sources

- T. J. Haines and S. Rostami, "The Satake isomorphism for special maximal parahoric Hecke algebras",
  arXiv:0907.4506 (version 2): Abstract, Introduction, pp. 1–2 (the Satake isomorphism
  $\mathcal{H}_{\tilde K} \cong \mathbb{C}[X_*(A)]^W$ and the Cartan decomposition for unramified groups, after Cartier; for
  general connected reductive groups, Cartier's $\mathcal{H}_{\tilde K} \cong \mathbb{C}[\tilde\Lambda_M]^W$ and
  $\tilde K \backslash G(F) / \tilde K \cong W \backslash \tilde\Lambda_M$), Theorem 1.0.1 with the paragraph after it, and §9.2, (9.2.2), p. 11 (the
  Satake transform, with $dn$ giving $N(F) \cap K(F)$ measure $1$; $N(F) \cap K = N(F) \cap \tilde K$, since $N(F)$ lies in the kernel
  of the Kottwitz homomorphism $\kappa$: each $n \in N(F)$ is contracted to $1$ by conjugation by powers of a suitable element
  $a \in A(F)$, and $\kappa$ is locally constant with $\kappa(a^k n a^{-k}) = \kappa(n)$; this is a property of $N(F)$, not of all unipotent
  elements).
- P. Cartier, "Representations of p-adic groups: a survey", Proc. Sympos. Pure Math. 33, Part 1, 1979, 111–155,
  as cited by Haines and Rostami ([Car]).
