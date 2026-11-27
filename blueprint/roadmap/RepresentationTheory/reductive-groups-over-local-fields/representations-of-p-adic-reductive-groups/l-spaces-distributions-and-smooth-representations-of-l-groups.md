# ℓ-spaces, distributions and smooth representations of ℓ-groups

This node is still to be broken down. It covers the analysis on totally disconnected spaces and the definitions of
smooth representations that the pages on $p$-adic groups and the Weil representation use. An $\ell$-space is a
Hausdorff, locally compact topological space in which every point has a basis of compact open neighbourhoods; an
$\ell$-group is a [topological group](../../../Topology/topological-groups/topological-group.md) whose underlying space is an $\ell$-space.

- **Schwartz–Bruhat functions.** For an $\ell$-space $X$, $S(X)$ is the space of locally constant compactly
  supported functions $X \to \mathbb{C}$. For $Y \subseteq X$ open with closed complement $Z$, extension by zero and
  restriction give an exact sequence $0 \to S(Y) \to S(X) \to S(Z) \to 0$, and dually an exact sequence of the spaces
  of distributions, the linear forms on $S$: $0 \to S^*(Z) \to S^*(X) \to S^*(Y) \to 0$.
- **ℓ-sheaves.** An $\ell$-sheaf on $X$ is given by a non-degenerate $S(X)$-module; its distributions, supports and
  restrictions to locally closed subsets obey the same exact sequences.
- **Invariant distributions** (Gelfand–Kazhdan). A subset of a topological space is constructive if it is a finite
  union of locally closed subsets, and an action of $G$ on $X$ is constructive if its graph, the set of pairs $(x, gx)$,
  is constructive in $X \times X$. Let an $\ell$-group $G$ act constructively on an $\ell$-sheaf $(X, \mathcal{F})$. If no $G$-orbit carries a nonzero $G$-invariant $\mathcal{F}$-distribution, there are none on $X$.
  If an isomorphism $\sigma$ of $(X, \mathcal{F})$ normalizes the action, has a power acting through an element of
  $G$, and fixes every orbit carrying a nonzero invariant distribution together with those distributions, then every
  $G$-invariant $\mathcal{F}$-distribution on $X$ is $\sigma$-invariant.
- **Smooth and admissible representations.** A representation $(\pi, V)$ of an $\ell$-group $G$ is smooth (algebraic,
  in Bernstein–Zelevinsky's term) if the stabilizer of every vector is open; it is admissible if moreover, for every
  open subgroup $K$, the space $V^K$ of $K$-fixed vectors is finite dimensional. The smooth part of any representation
  is a subrepresentation, and the smooth representations with the intertwining maps form a category.

## Expansion

A good expansion has definition pages for $\ell$-spaces, $\ell$-groups, Schwartz–Bruhat functions and distributions,
$\ell$-sheaves, and smooth and admissible representations, and statement pages for the exact sequences and for the
two theorems on invariant distributions, each citing the sources below with locators. Bernstein and Zelevinsky prove
the theorems on invariant distributions by localization over a Hausdorff space of orbits (§§2.36–2.37) and by
induction over the open strata of a constructive action, on which the action is regular (§§6.4 and 6.6–6.10).

## Depends on

- [Topological group](../../../Topology/topological-groups/topological-group.md), for $\ell$-groups

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Representations of the group GL(n, F), where F is a local
  non-Archimedean field", Uspekhi Mat. Nauk 31 (1976), no. 3, 5–70; English translation Russian Math. Surveys
  31:3 (1976), 1–68: Chapter I, §1, 1.1 ($\ell$-spaces), 1.7 (Schwartz–Bruhat functions), 1.8 and 1.9 (the exact sequences),
  1.13–1.16 ($\ell$-sheaves and their distributions), pp. 6–10; §2, 2.1 (algebraic and admissible representations),
  p. 14; Chapter III, §6, 6.6, Definition, p. 53 (constructive subsets and actions), and Theorem 6.9 and Theorem 6.10
  (Gelfand and Kazhdan), pp. 54–55.
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.1 ($\ell$-groups) and §5.3 ($\ell$-spaces, $C^\infty(X)$ and $S(X)$).
