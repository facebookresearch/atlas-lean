# Language emptiness of parametric timed automata with one integer parameter and three clocks is undecidable

No algorithm decides whether some integer value of a single parameter makes the language of a parametric timed automaton with three clocks nonempty, or empty, in continuous as well as discrete time.

In a [parametric timed automaton](parametric-timed-automata.md), guards and invariants compare clocks with integer constants or with parameters; here parameter valuations are *nonnegative integers*, while clocks take nonnegative real values (continuous time) or integer values (discrete time). A clock is *parametric* if it is compared with a parameter somewhere, and *nonparametric* otherwise. The *reachability problem* asks whether some parameter valuation makes the language of the resulting timed automaton nonempty; the *safety problem* asks whether some parameter valuation makes it empty.

**Theorem.** The reachability and safety problems are undecidable for parametric timed automata with one integer parameter, three parametric clocks and no further nonparametric clocks, both in the continuous-time and in the discrete-time semantics (Theorem 1 of the source).

This tightens the undecidability for three parametric clocks and six parameters of Alur, Henzinger and Vardi. By contrast, for one parametric clock with any number of integer parameters and nonparametric clocks both problems are decidable in continuous time (reachability in NEXPTIME), extending the discrete-time decidability of Alur, Henzinger and Vardi; with real-valued parameters, a single parameter already gives undecidability (Miller).

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Reachability is reduced from halting of two-counter Minsky machines and safety from their boundedness problem, also undecidable. The automaton uses the parameter $p$ and three parametric clocks $x_1,x_2,z$: whenever it is in a location $\ell_i$ with $z=0$, the values of $x_1,x_2$ equal the two counters and $i$ is the next instruction. Gadgets for increment and for test-and-decrement keep this invariant as long as the counters stay below $p$; a halting computation reaches the accepting location for a large enough $p$, while for safety the accepting location is reachable iff the computation exceeds the bound $p$. All guards are exact, so transitions are taken only after integer delays and the result holds in both semantics.

## Sources

- Nikola Beneš, Peter Bezděk, Kim G. Larsen and Jiří Srba, "Language Emptiness of Continuous-Time Parametric Timed Automata", in *Automata, Languages, and Programming (ICALP 2015)*, Lecture Notes in Computer Science 9135, 2015, pp. 69–81, doi:[10.1007/978-3-662-47666-6_6](https://doi.org/10.1007/978-3-662-47666-6_6); read in arXiv:1504.07838v1 ([arXiv](https://arxiv.org/abs/1504.07838v1)), whose numbering is used: Section 1 (Table 1), Section 2 (parametric timed automata, reachability and safety), Section 3 (the reduction from Minsky machines and Theorem 1) and Section 4 (decidability for one parametric clock).
