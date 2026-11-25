# Cap product of singular homology with singular cohomology

Let $X$ be a topological space and $R$ a commutative ring with identity. Use ordinary (unreduced) singular chains $C_k(X; R)$, which are zero in negative degrees. For a singular $k$-simplex $\sigma\colon \Delta^k \to X$ and a singular cochain $\varphi \in C^l(X; R)$ with $k \ge l \ge 0$, set $\sigma \frown \varphi = \varphi(\sigma|[v_0, \dots, v_l])\, \sigma|[v_l, \dots, v_k] \in C_{k-l}(X; R)$. Here $\sigma|[v_i, \dots, v_j]$ is the restriction of $\sigma$ to that face, identified with a standard simplex. For $k < l$ set $\sigma \frown \varphi = 0$. Extending $R$-bilinearly gives the *cap product* $C_k(X; R) \times C^l(X; R) \to C_{k-l}(X; R)$ of chains with cochains. With these conventions the boundary formula $\partial(\sigma \frown \varphi) = (-1)^l(\partial \sigma \frown \varphi - \sigma \frown \delta\varphi)$ holds for all $k$ and $l$. It shows that the cap product of a cycle and a cocycle is a cycle, and that its homology class does not change when either factor changes by a boundary or a coboundary. The cap product therefore induces an $R$-bilinear *cap product* $H_k(X; R) \times H^l(X; R) \to H_{k-l}(X; R)$, $([c], [\varphi]) \mapsto [c \frown \varphi]$. The boundary formula is used only for this descent to homology; the chain-level operation is defined directly.

## Expansion

A good expansion of this node links each notion it is built from: the boundary formula for the cap product; singular homology with coefficients.

## Depends on

- [Commutative ring with identity: a ring whose multiplication is commutative and has an identity element 1](../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Topological space](../topological-spaces/topological-space.md)
- [Singular cohomology with coefficients in an abelian group](singular-cohomology-coefficients.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 3.3.
