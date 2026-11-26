# Square-grid contraction separates border circuits under graph border necessity

For a finite loopless multigraph with separately named edges, use a distinct indeterminate $X_{v,a}$ for each vertex $v$ and each labeling $a$ of its incident edges by $[n]$. Sum, over all labelings $\ell$ of the edges by $[n]$, the products $\prod_v X_{v,\ell|_{\operatorname{Inc}(v)}}$. Take this polynomial on the $n$-by-$n$ square grid with its horizontal and vertical nearest-neighbor edges, separately for each $n\ge0$. Its selected coefficient degree is the number of vertices, $n^2$.

Fix a field $F$ and assume the following graph border necessity over $F$. For **every** family of finite loopless multigraphs of polynomially bounded vertex count, a polynomial-size degree-component border formula bound implies uniformly bounded component sizes and degrees; a polynomial-size degree-component border affine-branching-program bound implies uniformly bounded cutwidth; and a polynomial-size degree-component border circuit bound implies uniformly bounded treewidth and degrees. Each border bound uses the degree equal to the vertex count and allows outputs of unrestricted total degree before coefficient projection. Formula size charges binary $+,-,\times$ nodes in a tree; an affine branching program has a designated first row of value one and later rows, each valued by the sum of earlier-row values times the affine labels of the incoming edges. A later row with no incoming edges has value zero. The output is a designated row; size counts vertices plus edges, including parallel edges separately. Cutwidth is a minimum over vertex orderings of the largest number of crossing edges at a cut; treewidth uses a finite tree decomposition with bags of size at most one more than the width. All polynomial bounds and uniform bounds are in the family index, not the size of an individual bag or cut.

Under this hypothesis, the square-grid family belongs to exact $\mathsf{VNP}_F$, does not belong to exact $\mathsf{VP}_F$, and has no polynomially bounded family of [degree-component border circuits](degree-component-border-circuits.md). Exact VP uses polynomial bounds on variables, degree and circuit size; VNP sums such a verifier over all Boolean assignments on polynomially bounded witness variables. This is a conditional result; it does not discharge graph border necessity or give a quantitative grid exponent.

## Depends on

- [Degree-component border circuits](degree-component-border-circuits.md), graph contraction, and all three clauses of the stated graph border necessity hypothesis.

## Proof depends on

- Unbounded treewidth of the square grids, VNP membership for bounded-degree polynomial-order graph contractions, and the passage from an exact circuit to a degree-component border witness.

## Expansion

Formalize the edge-label and vertex-table conventions, the three border modes, and the conditional argument. The proof uses the circuit clause, but the source's full hypothesis is retained. Use the row-column intersection argument for unbounded width; leave any independent proof of graph border necessity separate.

## Sources

- OpenAI, [Conditional conclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/GridSeparation.lean#L12-L22), [Border assumptions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/GraphClassification.lean#L18-L84), [Contraction model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/GraphContractions.lean#L12-L52), [Affine branching program rows and cost](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/Models.lean#L57-L89), and [Square-grid indexing](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/GridGraph.lean#L10-L23).
