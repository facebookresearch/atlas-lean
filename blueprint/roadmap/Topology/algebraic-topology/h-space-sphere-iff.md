# Adams' theorem on spheres that are H-spaces

For every natural number $n$, the unit sphere
$S^n$ of the Euclidean space $\mathbb{R}^{n+1}$ admits an H-space structure if and only if
$n = 0$, $n = 1$, $n = 3$ or $n = 7$. Here an H-space structure on $S^n$ is a continuous map
$\mu \colon S^n \times S^n \to S^n$ together with a point $e \in S^n$ such that
$\mu(e, e) = e$ and the maps $x \mapsto \mu(e, x)$ and $x \mapsto \mu(x, e)$ are both homotopic
to the identity relative to $\{e\}$.

## Sources

- J. F. Adams, 'On the non-existence of elements of Hopf invariant one', Ann. of Math. 72 (1960), 20-104; J. F. Adams and M. F. Atiyah, 'K-theory and the Hopf invariant', Quart. J. Math. Oxford 17 (1966), 31-38. See also A. Hatcher, 'Algebraic Topology', Section 4.B. Via leanprover/lean-eval@38361be, problem `hSpace_sphere_iff`.
