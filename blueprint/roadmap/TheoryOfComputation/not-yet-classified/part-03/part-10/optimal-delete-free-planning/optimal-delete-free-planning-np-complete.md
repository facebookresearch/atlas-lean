# OPTIMAL DELETE-FREE PLANNING is NP-complete

An instance is a propositional STRIPS task without delete lists, given by actions $o = (\mathrm{pre}(o), \mathrm{add}(o))$, an initial state $I$ and goals $G$ (finite sets of atoms), together with a bound $K \in \mathbb N$. Applying $o$ to a state $S$ gives $S \cup \mathrm{add}(o)$ when $\mathrm{pre}(o) \subseteq S$ and is undefined otherwise. The question is whether some sequence of at most $K$ actions, applied from left to right to $I$, reaches a state containing $G$. Instances are encoded as bitstrings, and bitstrings that do not decode are no-instances. The statement is that this problem is in NP and every NP problem reduces to it by a polynomial-time many-one reduction.

## Sources

- T. Bylander, The computational complexity of propositional STRIPS planning, Artificial Intelligence 69 (1994), 165–204.
- J. Hoffmann and B. Nebel, The FF planning system: fast plan generation through heuristic search, Journal of Artificial Intelligence Research 14 (2001), 253–302.
