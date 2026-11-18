# GHS gap of a sourced current

Let $V$ and $\iota$ be finite sets and let each index $i \in \iota$ label an edge with endpoints $\mathrm{ends}(i)$, an unordered pair of elements of $V$ (loops allowed); a current is a finite set of edge indices, and let $m$ be a current, $\varphi$ a real function on subsets of $m$, $A \subseteq V$
and $o, x, y \in V$. With the [mass](aie-mass.md) $\mathrm{mass}_m(S) = \sum_{K \subseteq m,\ \partial K = S} \varphi(K)$, with $\partial K$ the set of sources of $K$, the GHS gap is

$$\mathrm{mass}_m(A) - \mathrm{mass}_m(A \triangle \{x, y\}) - \mathrm{mass}_m(A \triangle \{o, y\}) - \mathrm{mass}_m(A \triangle \{o, x\}).$$
