# Feasibility for optimal delete-free planning

An instance consists of actions $o$ with precondition set $\mathrm{pre}(o)$ and add set $\mathrm{add}(o)$, an initial state $I$, a goal set $G$ and a bound $K$. Applying $o$ to a state $S$ with $\mathrm{pre}(o) \subseteq S$ gives $S \cup \mathrm{add}(o)$, and is undefined otherwise. The instance is feasible when some sequence of at most $K$ actions (repetitions allowed) applies successfully from $I$ and reaches a state containing $G$.
