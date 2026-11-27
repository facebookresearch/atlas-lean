# Functional weighted automata and quantitative language realizability

A weighted automaton over finite words with sum, average or ratio measure is functional if all accepting runs on a word
have the same value; realizability asks whether a controller, alternating letters with an environment, can force a finite
play of value above a threshold.

**Quantitative languages.** Fix a finite alphabet $\Sigma$ containing a terminal symbol $\dashv$; words are read in the form
$u \dashv$ with $u \in (\Sigma \setminus \{\dashv\})^*$. For integers $v_0, \dots, v_n$ let
$\mathrm{Sum}(v) = \sum_i v_i$ and $\mathrm{Avg}(v) = \mathrm{Sum}(v)/(n + 1)$; for pairs $(r_i, c_i)$ of naturals with
$c_i > 0$ let $\mathrm{Ratio}(v) = \sum_i r_i / \sum_i c_i$.

**Automata.** For $V \in \{\mathrm{Sum}, \mathrm{Avg}, \mathrm{Ratio}\}$, a *$V$-automaton* $A = (Q, q_I, F, \delta, \gamma)$ is a
finite automaton whose transitions read letters other than $\dashv$ between non-final states, plus terminal transitions on
$\dashv$ into final states, with a weight function $\gamma$ on transitions (integers, or pairs of naturals with positive second
component for Ratio). The value of an accepting run is $V$ of its sequence of weights. $A$ is *functional* if all accepting
runs on the same word have the same value; it then defines the *quantitative language* $L_A$ mapping each word in its domain
to that value (and other words to an undefined value below every rational).

**Realizability.** Let $\Sigma$ be split into disjoint alphabets $\Sigma_I$ (environment) and $\Sigma_O$ (controller) with
$\dashv \in \Sigma_O$, and let the states of $A$ be split into $Q_O$ and $Q_I$ with $F \subseteq Q_I$ and transitions from
$Q_O$ on letters of $\Sigma_O$ to $Q_I$ and from $Q_I$ on letters of $\Sigma_I$ to $Q_O$. In the *realizability game* the
environment plays $i_0 \in \Sigma_I$, the controller answers $o_0 \in \Sigma_O$, and so on; the controller may end the play by
playing $\dashv$. A controller strategy is *winning* for a threshold $\nu \ge 0$ if against every environment strategy the play
is finite and its value $L_A$ exceeds $\nu$. The *quantitative language realizability problem* asks, given $A$ and $\nu$,
whether the controller has a winning strategy.

## Depends on

None.

## Proof depends on

None.

## Expansion

For deterministic Sum-, Avg- and Ratio-automata the realizability game is a finite game with quantitative objectives and is
decidable; functionality of these automata is decidable as well.

## Sources

- E. Filiot, R. Gentilini, J.-F. Raskin, "Quantitative languages defined by functional automata", *Logical Methods in Computer Science* 11(3), article 14, 2015, doi:[10.2168/LMCS-11(3:14)2015](https://doi.org/10.2168/LMCS-11(3:14)2015). Numbering of the version read, arXiv:1111.0862v4: Section 2 (quantitative languages, the measures Sum, Avg and Ratio, weighted automata, functionality) and Section 5 (the realizability game and problem).
