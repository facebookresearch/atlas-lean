# Muller presentation of a Rabin automaton

Given a Rabin automaton with set of Rabin
pairs $\mathcal{R}$, this is the Muller automaton with the same states, initial states and
transitions whose accepting family consists of the sets $S$ of states for which some pair
$(E, F) \in \mathcal{R}$ satisfies $S \cap E \neq \emptyset$ and $S \cap F = \emptyset$. A
Muller automaton accepts a run when the set of states that the run visits infinitely often
belongs to its accepting family.
