# Hensel's lemma with a derivative bound

Let $A$ be a discrete valuation ring with maximal
ideal $\mathfrak{m}$ that is complete and Hausdorff for the $\mathfrak{m}$-adic topology, and let
$v \colon A \to \mathbb{N} \cup \{\infty\}$ be its normalized additive valuation. Let $f \in A[X]$
have derivative $f'$, and let $a_0 \in A$ satisfy $2 v(f'(a_0)) < v(f(a_0))$. Then $f$ has a root
$a \in A$ such that $a - a_0 \in \mathfrak{m}$, $v(f'(a_0)) < v(a - a_0)$,
$v(f(a_0)) \le v(a - a_0) + 2 v(f'(a_0))$ and $v(f'(a)) = v(f'(a_0))$. Moreover, every root
$a' \in A$ of $f$ with $v(f'(a_0)) < v(a' - a_0)$ equals $a$.

## Sources

- ATLAS Hensel endpoint; the published statement dropped the condition $v(f'(a_0)) < v(a - a_0)$ on the root, which is kept here so that uniqueness applies to it.
