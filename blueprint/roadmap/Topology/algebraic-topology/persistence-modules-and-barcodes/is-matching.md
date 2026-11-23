# $\delta$-matching of barcodes

Let $(I_i)_{i \in \iota}$ and $(J_j)_{j \in \kappa}$ be two families of subsets of $\mathbb{R}$ (in
applications, the bars of two interval-decomposable persistence modules, with multiplicity), and
let $\delta \in \mathbb{R}$. A $\delta$-matching exists when $\delta \ge 0$ and there is a partial
bijection $M$ between the indices such that matched bars are within Hausdorff distance $\delta$,
and every unmatched bar lies in a closed interval $[a, a + 2\delta]$, so it has length at most
$2\delta$, that is, it lies within $\delta$ of the diagonal (Chazal, de Silva, Glisse and Oudot,
arXiv:1207.3674, §4.2, the definition of a partial matching and of a $\delta$-matching, for the
undecorated diagrams). For intervals of $\mathbb{R}$, the Hausdorff distance is the $\ell^\infty$
distance between the endpoint pairs, with infinite endpoints compared as in the source.

The scale is required to be nonnegative, as for interleavings (§3.2, "Let $\delta \ge 0$"): the
bottleneck distance is an infimum over such $\delta$. The identification of the Hausdorff
distance with the endpoint distance is for nonempty order-connected sets; for closed bounded
intervals it is [the Hausdorff distance between closed intervals](hausdorff-edist-icc-icc.md).
The Hausdorff distance between two sets equals the one between their closures, so it ignores
open or closed ends, as the undecorated diagram does.
