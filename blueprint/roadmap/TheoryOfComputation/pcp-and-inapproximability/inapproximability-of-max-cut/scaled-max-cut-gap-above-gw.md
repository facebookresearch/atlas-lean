# Scaled Max-Cut gaps above the Goemans–Williamson constant

Let $\alpha_{\mathrm{GW}}=\inf_{-1\le\rho<1}2\arccos(\rho)/(\pi(1-\rho))$. For each real $\alpha$ with $\alpha_{\mathrm{GW}}<\alpha\le1$, there are rational numbers $a>0$ and $b\ge0$ with $b<\alpha a$ and one deterministic finite-stack machine with finite stack alphabets. In polynomial time in the original input bit length it takes a binary word $x$ to a finite simple unweighted graph $G_x$ and a positive integer $Q_x$. If $x$ encodes a satisfiable three-slot CNF, then $\operatorname{MaxCut}(G_x)/Q_x\ge a$; for every other word, including malformed encodings, $\operatorname{MaxCut}(G_x)/Q_x\le b$. The maximum is over Boolean partitions and counts each crossing unordered edge once. The output starts with the framed binary vertex count and the framed scale and then lists the full row-major Boolean adjacency table. The scale need not be the edge count.

Input clauses have three signed literals with canonically framed little-endian binary natural variable names (a leading $1$ per digit and a closing $0$); a leading $1$ introduces each clause and $0$ ends the clause list. Decoding requires exhaustion of the input.

## Depends on

- [The Goemans–Williamson constant](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/gw-constant.md); the change of variable $\rho=\cos\theta$ identifies the infimum domains.

## Proof depends on

- Translation-game gap hardness, a quantitative cut-gap construction and its unweighted simple-graph realization, including normalization by the actual output scale.

## Expansion

Formalize the rational separation certificate independently of the real approximation parameter. Prove the output graph conversion and both value inequalities before transporting the whole reduction through the bit-machine model. The ordinary no-PTAS result for Max-Cut does not provide this threshold or this output contract.

## Related topics

- [MAX-CUT feasibility](../../np-completeness/graph-coloring-and-partitioning/maximum-cut/max-cut-feasible.md) describes the decision predicate, not the scaled reduction output.

## Sources

- OpenAI, [source encodings, gap and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OptimalMaxCut.lean#L5-L154).
