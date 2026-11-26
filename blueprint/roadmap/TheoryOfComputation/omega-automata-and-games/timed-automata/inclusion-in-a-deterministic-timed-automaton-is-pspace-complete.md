# Inclusion in the language of a deterministic timed automaton is PSPACE-complete

Given a [timed Büchi automaton](timed-buchi-automata.md) $\mathcal{A}_1$ and a
[deterministic timed automaton](deterministic-timed-automata.md) $\mathcal{A}_2$ (with a Büchi or Muller acceptance condition)
over the same alphabet, deciding whether $L(\mathcal{A}_1) \subseteq L(\mathcal{A}_2)$ is PSPACE-complete. The algorithm
first completes $\mathcal{A}_2$ by a nonaccepting sink location, as in the complementation of deterministic timed automata, and then
searches the region automaton of the product of the two timed transition tables for a reachable progressive cycle that
meets the acceptance condition of $\mathcal{A}_1$ and the complement of that of $\mathcal{A}_2$; hardness holds already when
$\mathcal{A}_1$ is deterministic, because emptiness of deterministic timed automata is PSPACE-hard.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Deterministic timed automata](deterministic-timed-automata.md)

## Proof depends on

- [Deterministic timed Muller automata are closed under Boolean operations](deterministic-timed-muller-automata-are-closed-under-boolean.md)
- [Region abstraction decides reachability for timed automata](../../../Logic/temporal-logic/timed-and-infinite-state-verification/region-abstraction-decides-reachability-for.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 6.6 and its proof, and the discussion before it in Section 6.3.
