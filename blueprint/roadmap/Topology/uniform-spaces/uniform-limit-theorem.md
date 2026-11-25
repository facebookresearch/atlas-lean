# Uniform limits of continuous functions are continuous

If continuous functions from a topological space to a metric space converge uniformly, then the limit function is continuous; pointwise convergence alone would not be enough. Mathlib proves a more general version, for families converging along a filter with values in a uniform space. Let $X$ be a topological space, $Y$ a uniform space, $p$ a filter on an index set $I$, and let $F_i \colon X \to Y$ for $i \in I$ and $f \colon X \to Y$ be functions. Suppose that $F_i$ converges to $f$ uniformly along $p$: for every entourage $V$ of $Y$, the set of $i$ with $(f(x), F_i(x)) \in V$ for all $x \in X$ belongs to $p$. Suppose also that continuous members occur frequently along $p$: every member of $p$ contains some $i$ for which $F_i$ is continuous. Then $f$ is continuous. Neither completeness nor any separation property of $Y$ is assumed. For a sequence $(F_n)$ of continuous functions into a metric space, take $I = \mathbb{N}$ with the filter of sets containing all $n \ge N$ for some $N$, and $Y$ with the uniformity of its metric; every $F_n$ is continuous, so continuous members occur frequently, which gives the familiar statement.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for uniform convergence along a filter: `TendstoUniformly`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/UniformSpace/UniformConvergence.lean#L112-L117.
