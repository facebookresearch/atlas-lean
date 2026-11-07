# Smale conjecture (Hatcher), relative parametrized form

Let $n \ge 1$ and let $X$ be a
compact, Hausdorff, second-countable smooth manifold with boundary modelled on the
$n$-dimensional half-space, with boundary $\partial X$. Write $S^3$ for the unit sphere of
$\mathbb{R}^4$ and let the orthogonal group $O(4)$ act linearly on it. Let
$F, F' : X \times S^3 \to S^3$ be smooth maps with $F(x, F'(x, p)) = p$ and $F'(x, F(x, p)) = p$
for all $x \in X$ and $p \in S^3$, and let $\psi_\partial : \partial X \to O(4)$ be a continuous
map with $F(b, p) = \psi_\partial(b)\, p$ for all $b \in \partial X$ and $p \in S^3$. Then there
are a continuous map $\psi : X \to O(4)$ that agrees with $\psi_\partial$ on $\partial X$ and
smooth maps $H, H' : X \times [0, 1] \times S^3 \to S^3$ such that for all $x \in X$,
$t \in [0, 1]$ and $p \in S^3$ we have $H(x, t, H'(x, t, p)) = p$, $H'(x, t, H(x, t, p)) = p$,
$H(x, 0, p) = F(x, p)$ and $H(x, 1, p) = \psi(x)\, p$, and $H(b, t, p) = F(b, p)$ whenever
$b \in \partial X$.

Thus each $F(x, \cdot)$ is a diffeomorphism of $S^3$, and $H$ is a smooth isotopy through
diffeomorphisms, relative to $\partial X$, from the family $F$ to the linear family $\psi$.

## Sources

- A. Hatcher, A proof of the Smale conjecture, Diff(S3) = O(4), Ann. of Math. 117 (1983). Via leanprover/lean-eval@38361be, problem `smale_conjecture`.
