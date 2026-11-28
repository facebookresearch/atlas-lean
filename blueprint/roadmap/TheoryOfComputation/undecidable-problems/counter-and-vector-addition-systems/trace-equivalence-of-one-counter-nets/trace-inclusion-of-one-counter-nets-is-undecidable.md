# Trace inclusion and trace equivalence of one-counter nets are undecidable

No algorithm decides whether every finite action sequence that one process of a one-counter net can perform can also be performed by another, nor whether the two processes have the same traces; this answers a question about one-counter nets, which have no zero tests.

**One-counter nets.** A *one-counter net* $(Q, \mathrm{Act}, \delta)$ has a finite set $Q$ of control states, a finite set $\mathrm{Act}$ of actions and a transition relation $\delta \subseteq Q \times \mathrm{Act} \times \{-1, 0, 1\} \times Q$. It induces a labeled transition system on the processes $pm \in Q \times \mathbb{N}$: $pm \xrightarrow{a} p'm'$ if $(p, a, d, p') \in \delta$ and $m' = m + d \ge 0$. A one-counter automaton may in addition have transitions enabled only when the counter is $0$. The *traces* of a process $\alpha$ are $T(\alpha) = \{ w \in \mathrm{Act}^* : \alpha \xrightarrow{w} \beta \text{ for some } \beta \}$.

**Theorem (Hofman, Mayr and Totzke).** Given two processes $pm$ and $qn$ of one-counter nets, it is undecidable whether $T(pm) \subseteq T(qn)$, and it is undecidable whether $T(pm) = T(qn)$ (Theorem 20 of the source). An instance consists of the net or nets, given by their finite transition relations, the control states $p, q$ and the counter values $m, n \in \mathbb{N}$; two nets over the same actions can be joined into one by disjoint union.

The source states that weak trace inclusion, which ignores silent actions, is undecidable as well. Both problems were known to be undecidable for one-counter automata (Jančar, Moller and Sawa; Valiant), and their status for one-counter nets had been open. By contrast, the same paper proves that weak simulation is decidable for one-counter nets, and inclusion of the traces of a finite-state system in those of a one-counter net is decidable, since it is decidable for Petri nets (Jančar, Esparza and Moller, as cited in Section 8).

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces containment of weighted finite automata with natural-number rewards, where a word's value is the maximum over runs of the sum of rewards and $A$ is contained in $B$ if its value never exceeds that of $B$; that containment is undecidable by Theorem 4 of Almagor, Boker and Kupferman (related to the [undecidability of equivalence of max-plus weighted automata](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/equivalence-of-max-plus-weighted-automata-is-undecidable.md) of Krob). Each automaton becomes a one-counter net whose counter accumulates the reward, with an extra action $d$ that decrements the counter and is available from every state. A word $w$ with value $v$ in $A$ larger than its value in $B$ gives the trace $w d^v$ of the first net that the second cannot perform, and conversely; trace inclusion reduces to trace equivalence for such nondeterministic systems.

## Sources

- P. Hofman, R. Mayr and P. Totzke, "Decidability of weak simulation on one-counter nets", in: 28th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2013), IEEE, 2013, 203–212, https://doi.org/10.1109/LICS.2013.26; read in arXiv:1304.4104v2 (the abstract, the definition of one-counter automata and nets in Section 2, and Theorem 20 in Section 7 of arXiv:1304.4104v2).
