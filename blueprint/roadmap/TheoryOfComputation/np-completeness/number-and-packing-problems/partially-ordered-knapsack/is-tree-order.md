# Out-tree test for the order of a PARTIALLY ORDERED KNAPSACK instance

For an instance of PARTIALLY ORDERED KNAPSACK with elements $u_0, \dots, u_{n-1}$ (one for each listed (size, value) pair), write $u_a \prec u_b$ when the pair $(a, b)$ is listed in the order; listed pairs that name no element are ignored. The test holds when both of the following hold:

- any two predecessors of an element are equal or related: whenever $a \prec u$ and $b \prec u$, then $a = b$, $a \prec b$ or $b \prec a$;
- some element $r$ precedes every element other than itself: $r \prec u$ for every $u \ne r$.

The test needs at least one element, and by itself it does not require $\prec$ to be irreflexive or transitive: a single element with the listed pair $(0, 0)$ passes. Given a strict partial order, which the [well-formedness](well-formed.md) of these instances requires separately, the test holds exactly when $\prec$ is the proper-ancestor order of an out-tree rooted at $r$, so that $u' \prec u$ means that $u'$ is a proper ancestor of $u$.
