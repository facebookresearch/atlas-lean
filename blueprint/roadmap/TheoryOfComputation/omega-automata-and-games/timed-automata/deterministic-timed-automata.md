# Deterministic timed automata

A timed transition table $(\Sigma, S, S_0, C, E)$, as for [timed Büchi automata](timed-buchi-automata.md), is *deterministic*
if $|S_0| = 1$ and, for every state $s$ and letter $a$, any two edges $(s, s_1, a, \lambda_1, \delta_1)$ and
$(s, s_2, a, \lambda_2, \delta_2)$ of $E$ have mutually exclusive clock constraints: $\delta_1 \wedge \delta_2$ is unsatisfiable.
A timed Büchi or [timed Muller automaton](timed-muller-automata.md) is deterministic when its timed transition table is.
A deterministic timed transition table has at most one run over a given timed word.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Timed Muller automata](timed-muller-automata.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Definition 6.1 and Lemma 6.3.
