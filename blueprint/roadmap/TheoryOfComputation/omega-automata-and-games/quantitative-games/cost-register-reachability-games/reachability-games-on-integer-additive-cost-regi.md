# Reachability games on integer additive cost register automata are undecidable

No algorithm decides whether the system has a winning strategy within a given budget in a reachability game on an additive cost
register automaton with integer registers.

**Theorem.** Given an $\mathrm{ACRA}(\mathbb{Z})$ reachability game, in the sense of
[reachability games on additive cost register automata](reachability-games-on-additive-cost-register-aut.md), and a budget $k$, it is
undecidable whether the system has a winning strategy with budget $k$.

The reduction already uses the budget $k = 0$. With registers over $\mathbb{N}$, solving these games is EXPTIME-complete, so the
undecidability comes from integer, possibly negative, register updates.

## Depends on

- [Reachability games on additive cost register automata](reachability-games-on-additive-cost-register-aut.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

From a two-counter machine $M$, the *halting gadget* $G_M$ has the program locations of $M$ plus four challenge states, input symbols that
claim the signs of the two counters, and registers $v_i, m_i$ tracking each counter $c_i$ and its negation, and a register $z$ that stays
$0$. At a zero test the system claims the result and the environment may either follow the claimed branch or jump to a challenge state
whose output, $v_i + 1$ or $m_i$, exceeds the budget $0$ exactly when the claim was false. Halting locations output $z = 0$. So the system
wins with budget $0$ exactly when it can follow the run of $M$ honestly to a halting location, that is, when $M$ halts.

## Sources

- R. Alur and M. Raghothaman, "Decision problems for additive regular functions", in *Automata, Languages, and Programming (ICALP 2013), Part II*, Lecture Notes in Computer Science 7966, pp. 37–48, Springer, 2013, doi:10.1007/978-3-642-39212-2_7; read in arXiv:1304.7029v1: the undecidability theorem of Section 5 for $\mathrm{ACRA}(\mathbb{Z})$ reachability games with the halting-gadget definition before it, and the EXPTIME-completeness for $\mathrm{ACRA}(\mathbb{N})$ games in the same section.
