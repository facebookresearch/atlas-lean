# Conditioned domination condition over a set of currents

Let $V$ and $\iota$ be finite sets and let each index $i \in \iota$ label an edge with endpoints $\mathrm{ends}(i)$, an unordered pair of elements of $V$ (loops allowed); a current is a finite set of edge indices. Let $M$ be a finite set of currents, $A \subseteq V$, $o, x, y \in V$, and for each
current $m$ let $\Phi_m$ be a real function on sets of edge indices. The conditioned domination
condition is

$$2 \sum_{\substack{m \in M \\ m \text{ connects all three pairs}}} \mathrm{mass}_m(A) \le \sum_{\substack{m \in M \\ m \text{ connects none of the pairs}}} \mathrm{mass}_m(A),$$

with $\mathrm{mass}_m$ the [mass](aie-mass.md) for the weight $\Phi_m$ and the pairs $\{x, y\}$,
$\{o, y\}$, $\{o, x\}$ ([all connected](aie-all-conn.md), [none connected](aie-none-conn.md)).
