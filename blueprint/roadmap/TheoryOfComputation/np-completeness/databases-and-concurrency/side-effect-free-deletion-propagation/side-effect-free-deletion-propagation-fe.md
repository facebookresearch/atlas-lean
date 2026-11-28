# Feasible instances of SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view)

An instance of SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) with relations $R_1$, $R_2$, view $V$ and candidate target tuple $t$ is feasible when some sets of source tuples $T_1 \subseteq R_1$ and $T_2 \subseteq R_2$ satisfy

$$
V(R_1 \setminus T_1, R_2 \setminus T_2) = V(R_1, R_2) \setminus \{t\}.
$$

This does not require $t \in V(R_1, R_2)$: when $t$ is not in the view, the condition asks for a deletion that leaves the view unchanged, and deleting nothing always qualifies. Membership of $t$ in the view is a separate condition of well-formedness, which the decision problem also requires.
