# The value-1 problem for probabilistic automata is undecidable

There is no algorithm that decides, given a [probabilistic automaton](probabilistic-automata-and-cut-point-languages.md) $\mathcal{A}$, whether its value
$\sup_w P_{\mathcal{A}}(w)$ equals $1$, that is, whether some words are accepted with probability arbitrarily close to $1$ (Gimbert and Oualhadj). This settles a
special case of the isolation problem, whether a given cut-point is isolated, which is undecidable in general (Bertoni). The problem is decidable for
$\sharp$-acyclic probabilistic automata, those whose support graph, on the nonempty sets of states with edges given by the action of a letter or by
keeping only the recurrent states of a set stable under a letter, has no cycles other than self-loops.

## Depends on

- [Probabilistic automata and cut-point languages](probabilistic-automata-and-cut-point-languages.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](emptiness-problem-for-probabilistic-automata.md)

## Sources

- H. Gimbert and Y. Oualhadj, "Probabilistic automata on finite words: decidable and undecidable problems", *Proceedings of ICALP 2010*, Lecture Notes in Computer Science 6199, Springer, 2010 (version <https://hal.science/hal-00456538v2>): Section 3, Theorem 3 (Bertoni), Theorem 4 with Proposition 6, and Section 4, Definitions 4 and 5 and Theorem 5 (acyclic automata).
