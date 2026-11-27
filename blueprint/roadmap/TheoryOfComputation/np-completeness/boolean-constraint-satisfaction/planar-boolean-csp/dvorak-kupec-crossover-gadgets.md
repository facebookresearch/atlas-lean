# Dvořák–Kupec crossover gadgets

Let $\Gamma$ be a Boolean language whose relations are self-complementary, and suppose some nonempty relation $R \in \Gamma$ has a cyclic difference $dR$ that is not an even delta-matroid; since all tuples of $dR$ have even weight, $dR$ then exhibits a failed exchange (a *cyclic exchange obstruction*). Suppose also that disequality is planarly pp-definable. Then the four-ary crossing relation $\{(a,b,a,b)\}$, whose ports appear in the cyclic order $v_1, v_2, v_3, v_4$ and forces $v_1 = v_3$ and $v_2 = v_4$, is planarly pp-definable from $\Gamma$ by a fixed conjunction of copies of a normalized obstruction relation and disequality constraints. Consequently every instance of $\mathrm{CSP}(\Gamma)$ reduces in polynomial time to a planar one. Empty relations are ignored in the test: the empty relation is self-complementary but its cyclic difference is empty, hence not a delta-matroid, and it yields no crossover gadget (for $\Gamma$ consisting of the empty relation, disequality and not-all-equal, planar instances stay easy).

## Proof sketch

Normalize the obstruction by planar operations (cyclic rotation, adjacent identification, pinning and projection) to a standardized four-ary relation; verify the two conjunctions of the source figure by finite truth-table checks; then replace each crossing in a drawing of the incidence graph by the gadget.

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)
- [Primitive-positive definitions and gadgets](../../boolean-constraint-satisfaction/polymorphisms-of-boolean-relations/primitive-positive-definitions.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Theorem 15(2) (restating the Dvořák–Kupec hardness result).
- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
