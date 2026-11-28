# TCTL emptiness is undecidable for bounded parametric timed automata with parameters only in upper-bound invariants

For parametric timed automata whose parameters appear only in invariants of the form clock below a parametric bound, with every parameter ranging over a bounded interval, no algorithm decides whether some parameter valuation satisfies the nested TCTL formula $\mathsf{EG}\,\mathsf{AF}_{=0}\,p$; with arbitrary invariants even reachability emptiness is undecidable.

**Models.** Let $\mathcal{A}$ be a [parametric timed automaton](parametric-timed-automata.md) whose locations are labeled by sets of atomic propositions. $\mathcal{A}$ is a *PTA with only invariants* if every edge guard is true (all timing constraints, parametric or not, sit in the location invariants), and a *PTA with only upper-bound invariants* if moreover every inequality of every invariant has the form $x \lhd \sum_i \alpha_i p_i + d$ with ${\lhd} \in \{<, \le\}$, $\alpha_i \in \{0, 1\}$ and $d \in \mathbb{Z}$, the form of the source's parametric constraints. It is *bounded* if each parameter $p_i$ ranges over an interval $[a_i, b_i]$ with $a_i, b_i \in \mathbb{N}$.

**Logic and problems.** TCTL formulas, a timed extension of [CTL formulas](../../../../Logic/temporal-logic/computation-tree-logic/formula.md), are $\varphi ::= \top \mid p \mid \neg\varphi \mid \varphi \wedge \varphi \mid \mathsf{E}\varphi\,\mathsf{U}_{\bowtie c}\varphi \mid \mathsf{A}\varphi\,\mathsf{U}_{\bowtie c}\varphi$ with $c \in \mathbb{N}$, interpreted on the maximal runs of the timed automaton $v(\mathcal{A})$ obtained from a parameter valuation $v$; the time-bounded until requires the witness to occur after a duration satisfying $\bowtie c$. $\mathsf{EF}_{\bowtie c}\varphi = \mathsf{E}\top\,\mathsf{U}_{\bowtie c}\varphi$, $\mathsf{AF}_{\bowtie c}\varphi = \mathsf{A}\top\,\mathsf{U}_{\bowtie c}\varphi$ and $\mathsf{EG}_{\bowtie c}\varphi = \neg\mathsf{AF}_{\bowtie c}\neg\varphi$. For a formula $\varphi$, *$\varphi$-emptiness* asks, given $\mathcal{A}$, whether the set of valuations $v$ with $v(\mathcal{A}) \models \varphi$ is empty.

**Theorem (André, Lime and Ramparison).**

1. $\mathsf{EF}$-emptiness (reachability of a location) is undecidable for PTAs with only invariants (Theorem 1 of the source).
2. $\mathsf{EG}\,\mathsf{AF}_{=0}\,p$-emptiness, for an atomic proposition $p$, is undecidable for bounded PTAs with only upper-bound invariants (Theorem 4).

Hence the full TCTL-emptiness problem is undecidable for bounded PTAs with only upper-bound invariants, whereas the same paper shows that reachability ($\mathsf{EF}$) emptiness is decidable, with exact synthesis of the satisfying valuations, for PTAs with only upper-bound invariants and no parameter bounds (Theorems 2 and 3 of the source); for a bounded PTA, intersecting the set computed by Theorem 3 with the parameter bounds then decides $\mathsf{EF}$-emptiness.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [CTL formulas](../../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For item 1, every PTA without invariants is transformed into a PTA with only invariants that has the same reachable locations for every parameter valuation: each edge is split through a new intermediate location whose invariant is the edge's guard. $\mathsf{EF}$-emptiness is undecidable for PTAs without invariants (Alur, Henzinger and Vardi). For item 2 the paper reduces the boundedness problem for two-counter machines, whether the counter values stay bounded along the computation, which is undecidable: it builds a bounded PTA with only upper-bound invariants encoding the machine, adapting an encoding of André, Lime and Ramparison for upper-bound PTAs, such that $\mathsf{EG}\,\mathsf{AF}_{=0}\,p$-emptiness holds exactly when the counters remain bounded. A complete expansion links the undecidability of reachability emptiness for parametric timed automata and of boundedness for two-counter machines.

## Sources

- É. André, D. Lime and M. Ramparison, "On the expressive power of invariants in parametric timed automata", in *2019 24th International Conference on Engineering of Complex Computer Systems (ICECCS)*, IEEE, 2019, pp. 87–96, doi:10.1109/ICECCS.2019.00017; read in arXiv:1908.06633v1: the definitions of PTAs, bounded PTAs, PTAs with only invariants and with only upper-bound invariants, TCTL and TCTL-emptiness, the undecidability theorem for $\mathsf{EF}$-emptiness in the section on the power of invariants, and the theorem on $\mathsf{EG}\,\mathsf{AF}_{=0}$-emptiness for bounded PTAs with only upper-bound invariants.
