# Limit configurations of convergent cellular automata can be uncomputable

There are freezing cellular automata whose limit value and freezing time are uncomputable, convergent automata whose limit from a computable configuration is uncomputable, and two-dimensional freezing automata whose limit state sets are neither recursively enumerable nor co-recursively enumerable.

**Theorem (Ollinger and Theyssier).** For a [convergent](convergent-cellular-automata.md) cellular automaton $F$ with limit configurations $F^\omega(c)$ and freezing times $\tau(c,z)$, the *limit value problem* $\mathrm{LIMIT}_F$ maps a computable configuration $c$, given by a Turing machine, to $F^\omega(c)_0$, and the *freezing time problem* $\mathrm{TIME}_F$ maps it to $\tau(c,0)$; for a configuration $c$ and state $q$, $\chi_q(c)=\{z: c_z=q\}$.

1. There is a [freezing](freezing-cellular-automata.md) cellular automaton $F$ for which both $\mathrm{LIMIT}_F$ and $\mathrm{TIME}_F$ are uncomputable (Theorem 7).
2. There is a one-dimensional convergent cellular automaton $F$ and a computable configuration $c$ such that $F^\omega(c)$ is uncomputable (Theorem 9).
3. There is a two-dimensional freezing cellular automaton $F$, a finite configuration $c$ and a state $q$ such that $\chi_q(F^\omega(c))$ is neither recursively enumerable nor co-recursively enumerable (Corollary 1).

These are sharp in the following sense (Proposition 9): for convergent $F$ and computable $c$, each $\chi_q(F^\omega(c))$ is in $\Delta^0_2$, and for freezing $F$ it is recursively enumerable if $q$ is minimal and co-recursively enumerable if $q$ is maximal for the freezing order. In dimension one, [bounded-change](bounded-change-cellular-automata.md) automata map computable configurations to computable limits (Theorem 8), so item 2 needs convergent automata.

## Depends on

- [Freezing cellular automata](freezing-cellular-automata.md)
- [Bounded-change cellular automata](bounded-change-cellular-automata.md)
- [Convergent cellular automata](convergent-cellular-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Arithmetical class $\Delta_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-delta.md)

## Proof depends on

- [Reachability for one-dimensional freezing cellular automata is undecidable](cylinder-reachability-of-freezing-cellular.md)

## Expansion

For item 1, the automaton $F_M$ of the reachability theorem works: reaching the invariable halting state $h$ at the origin from a cylinder is equivalent to $F^\omega(c_u)_0=h$ for a canonical computable configuration $c_u$, and $\mathrm{LIMIT}_F$ and $\mathrm{TIME}_F$ are Turing equivalent for freezing automata. Item 2 uses a convergent construction combining a Turing machine component with shrinking working zones, run on a machine that enumerates the halting set. Item 3 uses directed self-assembly tile systems whose limit configurations encode a recursively enumerable set (Lathrop, Lutz, Patitz and Summers), read as two freezing automata $F_1,F_2$ for the sets $\{n:\pi_1(\phi(n))\in H\}$ and $\{n:\pi_2(\phi(n))\in H\}$, with $H$ the halting set and $\phi$ a computable bijection $\mathbb N\to\mathbb N^2$; in the product automaton, the state pairing acceptance in the first component with rejection in the second marks a set that is neither r.e. nor co-r.e. A good expansion adds pages for the Turing equivalence of $\mathrm{LIMIT}_F$ and $\mathrm{TIME}_F$ for freezing automata, for the convergent construction with shrinking working zones used in item 2, and for the limit configurations of directed self-assembly tile systems (Lathrop, Lutz, Patitz and Summers) used in item 3.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for theorems, propositions and corollaries): Section 5: Definition 7, Remark 1, Theorem 7, Proposition 9, Theorem 8, Theorem 9, Theorem 10 (recalled construction of Lathrop, Lutz, Patitz and Summers) and Corollary 1.
