# Büchi automata are closed under intersection

For finite-state nondeterministic Büchi automata $A_1$ and $A_2$ over the same alphabet, some
finite-state nondeterministic Büchi automaton $A$ satisfies $L_\omega(A) = L_\omega(A_1) \cap
L_\omega(A_2)$.

The plain product with accepting set $F_1 \times F_2$ is not enough: it requires the two runs to
visit accepting states at the same instants, and Vardi gives two automata accepting $a^\omega$
whose plain product is empty. The construction runs both automata and keeps a pointer to one
of the two tracks; the pointer moves to the other track whenever the track it points to visits
an accepting state, and the accepting states are those of $F_1 \times S_2$ with the pointer on
the first track. This is Vardi's Proposition 6, credited there to Choueka (1974). Allowing also
the states of $S_1 \times F_2$ with the pointer on the second track as accepting states gives the
same language.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 6 and the counterexample before it.
