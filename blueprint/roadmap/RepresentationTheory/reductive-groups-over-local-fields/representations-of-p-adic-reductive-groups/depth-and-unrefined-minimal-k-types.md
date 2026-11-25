# Depth and unrefined minimal K-types

Let $k$ be a non-archimedean local field of any characteristic with residue field $\mathfrak{f}$,
$\mathbf{G}$ a connected reductive group over $k$ and $\mathcal{G} = \mathbf{G}(k)$, and use the
Bruhat–Tits building $\mathcal{B}(\mathbf{G}, k)$, the parahoric subgroups $\mathcal{G}_x$, the
Moy–Prasad filtrations $\mathcal{G}_{x,r}$, $\mathcal{G}_{x,r+}$, the lattices
$\mathfrak{g}^*_{x,r}$ and the finite reductive groups
$\mathsf{M}_x(\mathfrak{f}) = \mathcal{G}_x/\mathcal{G}_{x,0+}$ of
[parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md).
For $r > 0$, a character $\chi$ of $\mathcal{G}_{x,r}/\mathcal{G}_{x,r+}$ corresponds to a coset
$X + \mathfrak{g}^*_{x,(-r)+}$ in $\mathfrak{g}^*_{x,-r}$, and $\chi$ is **nondegenerate** if this
coset contains no nilpotent element. An irreducible representation of $\mathsf{M}_x(\mathfrak{f})$
is cuspidal if it has no nonzero vector fixed by the rational points of the unipotent radical of
any proper parabolic subgroup over $\mathfrak{f}$, as for
[the finite general linear groups](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md).

- An **unrefined minimal K-type** of **depth** $r$ is a pair $(\mathcal{G}_{x,r}, \chi)$ where
  $x \in \mathcal{B}(\mathbf{G}, k)$, $r \ge 0$ is a real number and $\chi$ is a representation of
  $\mathcal{G}_{x,r}$ trivial on $\mathcal{G}_{x,r+}$ such that: if $r = 0$, $\chi$ is an irreducible
  cuspidal representation of $\mathsf{M}_x(\mathfrak{f}) = \mathcal{G}_x/\mathcal{G}_{x,0+}$ inflated
  to $\mathcal{G}_x$; if $r > 0$, then $\mathcal{G}_{x,r} \ne \mathcal{G}_{x,r+}$ and $\chi$ is a
  nondegenerate character of $\mathcal{G}_{x,r}/\mathcal{G}_{x,r+}$. A representation of
  $\mathcal{G}$ **contains** it if its restriction to $\mathcal{G}_{x,r}$ contains $\chi$.
  Moy and Prasad require $\mathcal{G}_{x,r} \ne \mathcal{G}_{x,r+}$ for $r = 0$ as well; that
  would leave no depth-zero type for the trivial character of $\mathbb{Q}_2^\times$, whose
  filtration has $\mathcal{G}_{x,0} = \mathbb{Z}_2^\times = 1 + 2\mathbb{Z}_2 = \mathcal{G}_{x,0+}$,
  although item 2 of the theorem below asserts one, so the condition is imposed here only in
  positive depth.
- Two unrefined minimal K-types $(\mathcal{G}_{x,r}, \chi)$ and $(\mathcal{G}_{y,s}, \xi)$ are
  **associates** if $r = s$ and: if $r = 0$, there is $g \in \mathcal{G}$ such that
  $\mathcal{G}_x \cap \mathcal{G}_{gy}$ surjects onto both $\mathsf{M}_x(\mathfrak{f})$ and
  $\mathsf{M}_{gy}(\mathfrak{f})$ and $\chi \cong \xi^g$; if $r > 0$, the $\mathcal{G}$-orbit of the
  coset realizing $\chi$ meets the coset realizing $\xi$.

**Theorem (Moy–Prasad).** For every irreducible admissible representation $(\pi, V_\pi)$ of
$\mathcal{G}$ there is a nonnegative rational number $\varrho(\pi)$, the **depth** of $\pi$, such
that:

1. for some $x \in \mathcal{B}(\mathbf{G}, k)$ the space of $\mathcal{G}_{x,\varrho(\pi)+}$-fixed
   vectors in $V_\pi$ is nonzero, and $\varrho(\pi)$ is the smallest number with this property;
2. for every $y \in \mathcal{B}(\mathbf{G}, k)$ such that the space $W$ of
   $\mathcal{G}_{y,\varrho(\pi)+}$-fixed vectors is nonzero: if $\varrho(\pi) = 0$, every irreducible
   $\mathcal{G}_y$-submodule of $W$ contains an unrefined minimal K-type of depth zero of a
   parahoric subgroup $\mathcal{G}_x \subseteq \mathcal{G}_y$; if $\varrho(\pi) > 0$, every
   irreducible $\mathcal{G}_{y,\varrho(\pi)}$-submodule of $W$ is an unrefined minimal K-type.

Moreover any two unrefined minimal K-types contained in $\pi$ are associates. In particular $\pi$
contains an unrefined minimal K-type of depth $\varrho(\pi)$.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the building, the parahoric subgroups, the Moy–Prasad filtrations, the lattices $\mathfrak{g}^*_{x,r}$ with the duality, nilpotent elements and the groups $\mathsf{M}_x(\mathfrak{f})$

## Proof depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the normality, commutator and duality properties of the filtrations

## Sources

- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §1 (introduction), §2.1 (setting), §3.1,
  §3.2 (parahoric subgroups and their filtrations for a reductive group), §3.4 (nilpotent elements,
  nondegenerate characters, unrefined minimal K-types and associates) and Theorem 3.5 (this
  statement).
- A. Moy and G. Prasad, "Unrefined minimal K-types for p-adic groups", Invent. Math. 116 (1994),
  393–408: Theorem 5.2, the case of absolutely quasi-simple, simply connected groups over fields of
  characteristic zero, which Theorem 3.5 of the 1996 paper generalizes "with the same proof"
  (Moy–Prasad 1996, §1 and §3.4).
