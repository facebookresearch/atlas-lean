# Geometric tilings and the domino problem on a set of tilings

Geometric tilings cover the plane with translates of finitely many topological disks; the domino problem on a set of such tilings asks whether
labeled copies of the shapes, subject to finitely many forbidden patterns, tile the plane so that the underlying shape tiling lies in the set.

**Shapes and tilings.** A *shape* is a closed topological disk in $\mathbb{R}^2$, and a *shapeset* $\mathcal{S}$ is a finite set of shapes. A *tiling* is a covering of the plane by countably
many shapes with disjoint interiors, and an *$\mathcal{S}$-tiling* is one in which every shape is a translate of a shape of $\mathcal{S}$. A *pattern* is a finite, simply connected set
of non-overlapping shapes, its *support* the union of its shapes. Two tilings are $\varepsilon$-close if they agree on the disk of radius $\varepsilon^{-1}$ up to a translation of norm at most $\varepsilon$.
A *geometric subshift* on $\mathcal{S}$ is a set of $\mathcal{S}$-tilings invariant under all translations of $\mathbb{R}^2$ and closed in this topology; the *purely geometric subshift* on $\mathcal{S}$ is the set of all
$\mathcal{S}$-tilings.

**Finite local complexity.** A set $X$ of tilings has *finite local complexity* (FLC) if for every compact $K \subset \mathbb{R}^2$ only finitely many patterns, up to translation, with support in $K$
appear in tilings of $X$; equivalently, only finitely many two-tile patterns appear. Edge-to-edge polygonal tilings have FLC, while the purely geometric subshift of a single
square does not, since rows can slide by arbitrary offsets.

**The domino problem on $X$.** A *symbolic-geometric tile* is a pair $(s, a)$ of a shape $s \in \mathcal{S}$ and a label $a$ from a finite alphabet $A$; a *tileset* is a set $\tau \subseteq \mathcal{S} \times A$,
and $\pi$ erases labels. For a set $X$ of $\mathcal{S}$-tilings, the *domino problem on $X$* asks, given $A$, a tileset $\tau$ and a finite set $G$ of forbidden $\tau$-patterns, whether some
$\tau$-tiling avoids every pattern of $G$ and has $\pi$-image in $X$. When $\mathcal{S}$ is a unit square and $X$ consists of the edge-to-edge square tilings, this is the classical domino
problem for [Wang tiles](../wang-tiles-and-valid-tilings.md).

## Depends on

- [Wang tiles and valid tilings](../wang-tiles-and-valid-tilings.md)

## Proof depends on

None.

## Sources

- B. Hellouin de Menibus, V. H. Lutfalla and P. Vanier, "Decision problems on geometric tilings", *Theoretical Computer Science* 1067, article 115756, 2026, doi:10.1016/j.tcs.2026.115756; read in arXiv:2409.11739v2: Section 2 (Definitions 3 and 7–12: geometric tilings, patterns, geometric subshifts, valid tilings, finite local complexity, symbolic-geometric tilings and the domino problem on a set of tilings), with the numbering of that version.
