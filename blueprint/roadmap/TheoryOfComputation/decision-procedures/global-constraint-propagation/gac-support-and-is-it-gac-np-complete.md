# GACSupport and IsItGAC are NP-complete

Deciding whether one value has a support on a global constraint, and deciding whether given domains are already generalized arc consistent, are NP-complete in general: both lie in NP for any constraint type with a uniform polynomial-time evaluator and polynomial-time recognizable encodings, and simple constraint types make each of them NP-hard under polynomial-time many-one reductions.

Let GACSupport and IsItGAC be the [decision problems of generalized arc consistency](gac-reasoning-problems.md), posed for a constraint type with encoded instances and one uniform polynomial-time evaluation algorithm, as on that page. The two concrete types below have polynomial-time recognizable encodings.

1. For every such constraint type $\mathcal C$ whose set of valid encodings is decidable in polynomial time, GACSupport($\mathcal C$) and IsItGAC($\mathcal C$) belong to NP. (For a type whose valid encodings are only promised, the same certificates place the problems in the promise version of NP; ordinary NP membership can fail, because deciding validity may itself be hard.)
2. Let $\mathcal C_{\to}$ be the type whose instances are encoded by a CNF formula $\varphi$ over Boolean variables $x_1,\dots,x_m$; the scope is $(X,x_1,\dots,x_m)$, all value labels are true and false, and the allowed tuples are those satisfying $X\to\varphi$. Then GACSupport($\mathcal C_{\to}$) is [NP-complete](../../complexity-classes/mahaney-s-theorem/npcomplete.md), NP-hardness holding under polynomial-time many-one reductions.
3. Let $\mathcal C_{2}$ be the type whose instances are encoded by a number $n\ge1$ of variables and a binary relation on $\{r,g,b\}$ for each pair of distinct variables; a tuple is allowed when every pair of its entries lies in the corresponding relation (one global constraint of arity $n$, not $\binom n2$ separate binary constraints). Then IsItGAC($\mathcal C_{2}$) is NP-complete, NP-hardness holding under polynomial-time many-one reductions.

IsItGAC on $\mathcal C_2$ asks whether a single global constraint is GAC on its domains; it is not the feasibility problem of a binary CSP, though the reduction below uses the same encoding of colourability.

## Depends on

- [Decision problems of generalized arc consistency](gac-reasoning-problems.md): the problems GACSupport and IsItGAC and the encoding model.
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md): the completeness notion.
- [Polynomial-time many-one reduction](../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md): the reductions in items 2 and 3.

## Proof depends on

- [3SAT is NP-complete](../../np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md): satisfiability of CNF formulas, which contains 3SAT, is NP-hard; used in item 2.
- [3-COLORABILITY OF C4-FREE GRAPHS is NP-complete](../../np-completeness/graph-coloring-and-partitioning/coloring-graphs-with-forbidden-subgraphs/three-colorability-c4-free-np-complete.md): this restriction of graph 3-colourability is NP-hard, and the identity map reduces it to 3-colourability of arbitrary finite graphs; used in item 3.

## Expansion

*Membership.* After checking in polynomial time that the input is a valid encoding, a support is a tuple checked by the uniform evaluator in polynomial time, so it is a polynomial certificate for GACSupport. For IsItGAC, a certificate consists of one support for each value of each domain, at most $\sum_i|D(X_i)|$ tuples.

*Item 2.* Map a CNF formula $\varphi$ to the instance $X\to\varphi$ with all domains $\{\mathrm{true},\mathrm{false}\}$ and the value $X=\mathrm{true}$. It has a support exactly when some assignment satisfies $\varphi$; the map is computable in polynomial time.

*Item 3.* Map a graph with vertices $x_1,\dots,x_n$ ($n\ge1$) to the instance with every domain $\{r,g,b\}$ and, for every pair $x_i,x_j$, the relation "different" if $x_ix_j$ is an edge and $\{r,g,b\}^2$ otherwise. Allowed tuples are proper 3-colourings. Permuting the three colours maps colourings to colourings, so $r$ has a support for $x_i$ iff $g$ does iff $b$ does iff the graph is 3-colourable. Hence the full domains are GAC exactly when the graph is 3-colourable.

The source states items 2 and 3 as Observations 1 and 2 with exactly these transformations; its general setting treats a constraint as any polynomial-time test, and the two types above are the ones its proofs build.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Transformations defined in §2; Observation 1 (GACSupport is NP-complete) and Observation 2 (IsItGAC is NP-complete) with their proofs, §3.2 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
