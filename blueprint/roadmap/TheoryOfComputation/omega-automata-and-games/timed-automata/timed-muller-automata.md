# Timed Muller automata

A *timed Muller automaton* is a tuple $(\Sigma, S, S_0, C, E, \mathcal{F})$ where $(\Sigma, S, S_0, C, E)$ is a timed transition
table, as for [timed Büchi automata](timed-buchi-automata.md), and $\mathcal{F} \subseteq 2^S$ is an *acceptance family*. A run
$r$ over a timed word is accepting when the set $\inf(r)$ of states it visits infinitely often belongs to $\mathcal{F}$, and
the automaton accepts the timed language of the timed words over which it has an accepting run.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Definition 3.18.
