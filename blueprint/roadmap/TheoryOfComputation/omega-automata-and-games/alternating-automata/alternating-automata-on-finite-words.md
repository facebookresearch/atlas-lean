# Alternating automata on finite words

For a set $X$, let $\mathcal{B}^+(X)$ be the set of positive Boolean formulas over $X$, built from the elements of $X$, $\mathrm{true}$ and $\mathrm{false}$
with $\wedge$ and $\vee$; a set $Y \subseteq X$ *satisfies* such a formula if it is true when the members of $Y$ are true and the other elements false.
An *alternating automaton* is a tuple $\mathcal{A} = (\Sigma, S, s_0, \rho, F)$ of a finite nonempty alphabet $\Sigma$, a finite nonempty set $S$ of states,
an initial state $s_0$, a set $F \subseteq S$ of accepting states and a transition function $\rho : S \times \Sigma \to \mathcal{B}^+(S)$. A *run* on a word
$a_0 \cdots a_{n-1}$ is a finite tree labelled by states, with root labelled $s_0$, such that every node $x$ at depth $i < n$ labelled $s$ has children whose
labels form a set satisfying $\rho(s, a_i)$. The run is *accepting* if every node at depth $n$ is labelled by a state of $F$, and $L(\mathcal{A})$ is the set
of words with an accepting run. A nondeterministic automaton is the special case in which every $\rho(s, a)$ is a disjunction of states.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Section 2.5, the definitions of positive Boolean formulas, alternating automata, runs and accepting runs.
