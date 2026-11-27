# Timed games under delayed control are undecidable

When a controller's actions in a timed game take effect only after a chosen delay, so that unboundedly many actions can be pending at once, no algorithm decides whether the controller has a strategy that reaches a target, or one that stays safe, even with one clock, no uncontrollable actions and one possible delay.

**Timed games under delayed control (Larsen and Zimmermann).** A *timed game under delayed control* $(\mathcal{A}, \Sigma_c, \Sigma_u, T, F)$ consists of a timed automaton $\mathcal{A}$ whose actions are split into *control actions* $\Sigma_c$ and *uncontrollable actions* $\Sigma_u$, a finite set $T \subseteq \mathbb{N}$ of allowed delays and a set $F$ of locations. A *schedule* is a finite sequence $(a_0, t_0) \cdots (a_{k-1}, t_{k-1})$ of control actions with timestamps, $t_0 \le \dots \le t_{k-1}$, and a state is a triple $(\ell, v, \sigma)$ of a location, a clock valuation and a schedule, starting from the empty schedule. From a state, time may pass by $\delta \le t_0$ (respecting the invariant), which decreases every timestamp by $\delta$; an uncontrollable edge may be taken; a *scheduling action* $(a, t)$ with $a \in \Sigma_c$, $t \in T$ may insert $(a, t)$ into the schedule; and when $t_0 = 0$ an edge labeled $a_0$ is taken and $(a_0, t_0)$ is removed. A strategy maps finite runs to scheduling actions or to waiting. It *satisfies reachability* if every maximal run consistent with it visits $F$, and *satisfies safety* if every run consistent with it stays in $F$. Schedules are unbounded: any number of actions may be pending.

**Theorem (Larsen and Zimmermann).** It is undecidable, given a timed game under delayed control, whether some strategy satisfies reachability (Theorem 1 of the source). The same holds for safety, and for safety together with time-divergence. Undecidability holds already for games with a single clock, no uncontrollable actions and $T = \{1\}$.

Ordinary timed games, the special case without delays, are decidable (EXPTIME-complete for reachability). With a bound, given in unary, on the number of pending actions the same source shows the reachability problem decidable in doubly exponential time, by reduction to ordinary timed games (Theorem 2).

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)
- [Timed games](../timed-games.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces termination of two-counter machines. The schedule serves as a queue: the counter values are the numbers of pending actions $0$ and $1$, followed by a divider action, all with timestamps in $(0, 1]$, and a gadget takes the first pending action and re-inserts it at the end with delay $1$. Gadgets for increment, decrement and zero test cycle through the queue once per instruction; the only choice left to the strategy is how long to wait during an increment, and a wrong choice leads to a losing sink. The target location is the stop instruction, so a strategy satisfying reachability exists exactly when the machine terminates; making every location except the sinks safe gives the safety version.

## Sources

- K. G. Larsen and M. Zimmermann, "You may delay, but time will not: timed games under delayed control", in: Design and Verification of Cyber-Physical Systems: From Theory to Applications, Lecture Notes in Computer Science, Springer, 2026, 24–47, https://doi.org/10.1007/978-3-032-16855-9_2; read in arXiv:2502.18972v1 (Section 3, Section 4 with Proposition 2 and Theorem 1 and the remarks after it, and Theorem 2 in Section 5 of arXiv:2502.18972v1, where the llncs class numbers each kind of statement separately).
