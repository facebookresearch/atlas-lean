# Muller presentation of a Streett automaton

Given a Streett automaton with set of
Streett pairs $\mathcal{P}$, this is the Muller automaton with the same states, initial states
and transitions whose accepting family consists of the sets $S$ of states such that every pair
$(E, F) \in \mathcal{P}$ with $S \cap E \neq \emptyset$ also satisfies $S \cap F \neq \emptyset$.
A Muller automaton accepts a run when the set of states that the run visits infinitely often
belongs to its accepting family.
