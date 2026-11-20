# The pair condition splits by vertex

For a mode $m$ and Booleans $b$, $s_i$, $s_j$, let
$\mathrm{ok}_m(b, s_i, s_j)$ be the pair condition of $m$: $\lnot(s_i \land s_j) \lor b$ for
clique, $\lnot(s_i \land s_j) \lor \lnot b$ for independent set and $\lnot b \lor s_i \lor s_j$
for vertex cover. Let $\mathrm{free}_m(s_i)$, the part that vertex $i$ alone settles, be
$\lnot s_i$ for clique and independent set and $s_i$ for vertex cover, and let
$\mathrm{sat}_m(b, s_j)$, the part left to $j$, be $\lnot s_j \lor b$ for clique,
$\lnot s_j \lor \lnot b$ for independent set and $\lnot b \lor s_j$ for vertex cover. Then for
every mode $m$ and all Booleans $b$, $s_i$, $s_j$, we have
$\mathrm{ok}_m(b, s_i, s_j) = \mathrm{free}_m(s_i) \lor \mathrm{sat}_m(b, s_j)$.
