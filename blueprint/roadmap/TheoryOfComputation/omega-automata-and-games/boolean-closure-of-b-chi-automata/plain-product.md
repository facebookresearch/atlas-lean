# Plain product of two Büchi automata

The plain product of Büchi automata $A_1$ and $A_2$ over the same alphabet, with accepting sets $F_1$
and $F_2$, runs both synchronously on the input and has accepting set $F_1 \times F_2$: a run is accepting when both
components are in accepting states at the same instants, infinitely often. Its states are the
pairs $(s_1, s_2)$ of states of $A_1$ and $A_2$, its initial states the pairs of initial states, and
it moves from $(s_1, s_2)$ to $(s_1', s_2')$ on a letter $a$ when $A_1$ moves from $s_1$ to $s_1'$ and
$A_2$ moves from $s_2$ to $s_2'$ on $a$.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, the automaton $A_1 \times A_2$ before Proposition 6.
