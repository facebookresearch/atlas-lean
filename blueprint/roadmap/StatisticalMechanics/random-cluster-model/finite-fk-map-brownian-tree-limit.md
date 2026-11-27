# Brownian continuum-tree limit of finite Fortuin–Kasteleyn maps

Fix $q>4$. At positive edge size $m$ use connected oriented-sphere rotation systems on $2m$ darts with root dart $0$: the edge reversal is a fixed-point-free involution, the rotation orbits are vertices, and the face permutation is rotation composed with reversal. The vertex and face counts sum to $m+2$. Quotient by simultaneous dart relabelling fixing $0$. Loops and multiple edges are allowed. Give each pair of rooted map $M$ and arbitrary edge subset $A$ probability proportional to

$$
q^{k_M(A)+(|A|-|V(M)|)/2},
$$

where $k_M(A)$ counts components including isolated vertices. Use the full map graph distance on vertices, not the distance in $A$, and probability given by pushing forward the uniform dart law to vertices (loops contribute two darts). Forget the root and decoration after sampling.

There is $c>0$ depending on $q$ such that with distance multiplied by $c/\sqrt m$ these compact metric probability spaces converge, through all positive $m$, to the standard Brownian continuum random tree in the bounded-continuous-test sense for Gromov–Hausdorff–Prokhorov distance. Explicitly, on any probability space with three independent real Brownian motions $B_i$, set $e(t)=(\sum_i(B_i(t)-tB_i(1))^2)^{1/2}$ for $t\in[0,1]$. Identify zero-distance pairs under $e(s)+e(t)-2\min_{[s\wedge t,s\vee t]}e$ and push forward uniform time. Expected values of every bounded test continuous on valid compact metric probability spaces for GHP converge to its Bochner expectation (zero under the native totalization when not integrable) on this excursion quotient. GHP is the infimum over common isometric embeddings of the maximum of Hausdorff and Lévy–Prokhorov distances of the embedded spaces and measures.

**Conventions.** Use rooted rotation-system quotients, the decorated FK finite law, the degree measure, the excursion pseudometric quotient and the measured GHP topology (not just Gromov–Hausdorff distance).

## Depends on

- [Rooted-map FK weight and vertex metric law](fk-rooted-map-metric-law.md)

## Proof depends on

A metric scaling-limit comparison for the FK map model at $q>4$, including distance error control and convergence of the mass distribution, and the Brownian excursion identification of the limiting tree.

## Expansion

Verify that rooting, relabelling and any use of representatives preserve the metric-measure law, and establish the map encoding and statistical scaling theorem before translating to GHP tests. Preserve all positive edge sizes and the normalized degree measure; no statement about diffusion, spectrum, or other $q$ regimes is included.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FKCRT.lean#L207-L210)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/211.md)
- [Accompanying manuscript: Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf)
