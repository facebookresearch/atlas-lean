# A contractible space has trivial reduced singular homology

Let $X$ be a contractible topological space, that is, a space homotopy equivalent to a one-point space (in particular $X$ is nonempty). Then its reduced singular homology groups with integer coefficients vanish: $\tilde H_n(X) = 0$ for every integer $n$.

## Proof sketch

For $n > 0$ the reduced group $\tilde H_n(X)$ equals $H_n(X)$. A homotopy equivalence induces isomorphisms on singular homology, so $H_n(X) \cong H_n(\mathrm{pt})$, and this is $0$ by the singular homology of a point. For $n = 0$, a contractible space is path-connected. For a path-connected space the augmentation induces an isomorphism $H_0(X) \to \mathbb{Z}$, so its kernel $\tilde H_0(X)$ is $0$. In degree $-1$ the augmented chain complex is $\mathbb{Z}$, and the augmentation $C_0(X) \to \mathbb{Z}$ is surjective because $X$ is nonempty, so $\tilde H_{-1}(X) = 0$. Below degree $-1$ the augmented chain complex is zero.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the path-connectedness of contractible spaces; the zeroth homology of a path-connected space; the homology of a point; the isomorphisms induced on homology by homotopy equivalences; reduced singular homology.

## Depends on

- [Contractible space](../contractibility-and-local-contractibility/contractible-space.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 2.1, the remark after Corollary 2.11.
