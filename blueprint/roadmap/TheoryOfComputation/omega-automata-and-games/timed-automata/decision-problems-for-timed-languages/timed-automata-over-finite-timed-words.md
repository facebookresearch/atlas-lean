# Timed automata over finite timed words

A timed automaton over finite timed words reads a finite sequence of delays and letters, constrains its transitions by clock
guards, and accepts by final states; the timed languages it accepts are the timed regular languages of finite timed words.

Let $\mathcal{R}$ be the set of positive real numbers and $\Sigma$ a finite alphabet. A *finite timed word* over $\Sigma$ is a
word $t_1 . a_1 . t_2 . a_2 \cdots t_n . a_n$ with $n \ge 0$, $t_i \in \mathcal{R}$ and $a_i \in \Sigma$: the letter $a_i$
occurs $t_i$ time units after the previous letter (after time $0$ for $a_1$). The set of finite timed words is the free monoid
$(\mathcal{R} \times \Sigma)^\star$, a *timed language* is a subset of it, and the complement of $L$ is
$L^c = (\mathcal{R} \times \Sigma)^\star \setminus L$.

A *timed automaton* $\mathcal{A}$ has a finite set of states, a finite set of start states, a set of final states, a finite set
of clocks and a finite set of transitions; each transition is labeled by a letter of $\Sigma$, carries a diagonal-free clock
constraint (a Boolean combination of comparisons of single clocks with rational constants, as for
[timed Büchi automata](../timed-buchi-automata.md)) and a set of clocks to reset to $0$; there are no $\varepsilon$-transitions.
All clocks start at $0$ and advance at rate $1$; reading $t . a$ lets $t$ time units elapse and then takes an $a$-labeled
transition whose constraint is satisfied, resetting its clocks. The automaton accepts a finite timed word if some run on it starts in
a start state and ends in a final state, and $L(\mathcal{A})$ is the set of accepted timed words. A timed language is *timed
regular* if it is $L(\mathcal{A})$ for some timed automaton. $\mathcal{A}$ is *deterministic* if it has one start state and
any two transitions leaving the same state with the same letter have mutually exclusive clock constraints; a deterministic
timed automaton has at most one run on each timed word.

$TA(n, K)$ denotes the class of timed automata with at most $n$ clocks whose constants are at most $K$. Timed regular
languages are closed under union and intersection but not under complementation; the languages of deterministic timed
automata are closed under complementation.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)

## Proof depends on

None.

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Section 2 of the version arXiv:0712.1363v1 (finite timed words as time-event sequences, timed automata with diagonal-free guards, determinism, timed regular languages).
