# Büchi automata are closed under union

For finite-state nondeterministic Büchi automata $A_1$ and $A_2$ over the same alphabet, some
finite-state nondeterministic Büchi automaton $A$ satisfies $L_\omega(A) = L_\omega(A_1) \cup
L_\omega(A_2)$.

The automaton is the disjoint union of $A_1$ and $A_2$: a run of the union is a run of one of
them, and it is accepting exactly when that run is. This is Vardi's Proposition 5, credited
there to Choueka (1974).

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 5.
