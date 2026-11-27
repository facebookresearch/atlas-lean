# Label Cover is NP-hard with perfect completeness and arbitrarily small soundness

For every $\delta > 0$ there are finite label sets $\beta, \gamma$ (with sizes depending only on $\delta$) such that $\mathrm{GapLabelCover}_{\beta,\gamma}(1, \delta)$ is NP-hard under polynomial-time many-one reductions.

## Proof sketch

Start from the NP-hard constant-gap binary CSP given by the PCP theorem, remove loops, apply the incidence reduction to Label Cover (gap at least a constant $\varepsilon$), and take the $k$-fold parallel repetition with $k$ chosen so that $(1 - \varepsilon^3/6000)^{k/\log(|\beta||\gamma|)} \le \delta$. For fixed $k$ the repetition is computable in polynomial time.

## Depends on

- [Label Cover (projection games)](label-cover-projection-games.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)
- [Incidence reduction from binary CSPs to Label Cover](incidence-reduction-from-binary-csps-to-label-cover.md)
- [Parallel repetition theorem (Raz, Holenstein)](parallel-repetition-theorem.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- R. Raz, "A Parallel Repetition Theorem", SIAM Journal on Computing 27(3), 1998.
