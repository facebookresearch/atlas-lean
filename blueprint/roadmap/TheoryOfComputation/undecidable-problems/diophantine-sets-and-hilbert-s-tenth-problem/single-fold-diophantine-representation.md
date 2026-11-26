# Single-fold Diophantine representations

For every natural $n\ge1$ and every recursively enumerable set $S\subseteq\mathbb N^n$, there
exist a natural $m\ge1$ and one polynomial $P\in\mathbb Z[X_1,\ldots,X_n,Y_1,\ldots,Y_m]$ such that
for every $a\in\mathbb N^n$,

$$
 a\in S\quad\Longleftrightarrow\quad \exists w\in\mathbb N^m:\ P(a,w)=0,
$$

and any two such $w$ are equal componentwise. Thus a member has exactly one complete tuple of
natural witnesses and a nonmember has none. All auxiliary coordinates are counted in $w$;
polynomial evaluation is over $\mathbb Z$. The endpoint does not separately state undecidability
of a promise problem.

## Expansion

Use the recursive-enumeration representation with unique auxiliary data and verify that all arithmetic gadgets and the final export to one integer polynomial preserve uniqueness of the full witness tuple. The ordinary DPRM theorem supplies existence but permits multiple witnesses.

## Sources

- [SingleFold.lean — `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SingleFold.lean#L24-L26)
- [ATLAS background: the ordinary DPRM theorem](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/blueprint/roadmap/TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
