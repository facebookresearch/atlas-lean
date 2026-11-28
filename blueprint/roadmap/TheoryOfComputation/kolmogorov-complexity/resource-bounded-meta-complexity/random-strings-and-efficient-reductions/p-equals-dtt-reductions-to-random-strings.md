# P is the class of decidable sets dtt-reducible to R_C for every universal machine

A decidable set that is disjunctive-truth-table reducible in time $t$ to $R_{C_U}$ for every universal machine $U$ is already computable in time $O(t^3)$; hence polynomial-time dtt reductions to the random strings, taken over all universal machines, characterize P.

For every computable time bound $t(n)\ge n$, every set in

$$
\mathrm{REC}\cap\bigcap_U\{A : A\le^{t(n)}_{dtt}R_{C_U}\}
$$

is computable in time $O(t^3(n))$, where $U$ ranges over universal Turing machines. Consequently

$$
\mathrm{P}=\mathrm{REC}\cap\bigcap_U\{A : A\le^{P}_{dtt}R_{C_U}\}.
$$

The intersection over $U$ is necessary: for every universal machine $U$ and every time-constructible $t(n)\ge n$ there is a recursive set $A\notin\mathrm{DSPACE}(t)$ with $A\le^P_{dtt}R_{C_U}$. For conjunctive and bounded truth-table reductions the decidable sets reducible to $R_C$ lie in P, and for monotone truth-table reductions they lie in P/poly. The analogous hypothesis for Turing reductions, $\mathrm{PSPACE}=\mathrm{REC}\cap\bigcap_U\mathrm{P}^{R_{C_U}}$, is stated as open.

## Expansion

Given a decidable $A$ not computable in time $O(t^3)$, the proof builds a universal machine $U$ by a stage construction: $U(00d)$ simulates a standard universal machine, which makes fewer than a quarter of each length non-random, and the remaining descriptions are assigned stage by stage. Stage $i$ defeats the $i$-th clocked dtt reduction by finding inputs $x_0\notin A$ and $x_1\in A$ whose short queries agree and then assigns short descriptions to their long queries so that the reduction gives the same answer on both inputs and therefore errs on one of them. The lower bound with fixed $U$ follows from Kummer's dtt reduction of the complement of the halting problem to $R_C$.

## Depends on

- [Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}](kolmogorov-random-strings.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Deterministic space classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman and Michal Koucký, "What Can Be Efficiently Reduced to the Kolmogorov-Random Strings?", *Annals of Pure and Applied Logic* 138(1–3), 2006, [doi:10.1016/j.apal.2005.06.003](https://doi.org/10.1016/j.apal.2005.06.003) (Hypothesis 4, Theorem 5, Theorem 7, Theorem 13, Theorem 15; numbering of the ECCC TR04-044 version).
