# The WS$k$S-definable tree languages are the recognizable ones

Let $\mathcal{F}$ be a ranked alphabet whose symbols have arity at most $k$. Code a ground term $t$ over $\mathcal{F}$ by the
tuple of finite sets of words in $\{1, \dots, k\}^*$ consisting of its set of positions and, for each $f \in \mathcal{F}$, the
set of positions labelled $f$. A set $L$ of ground terms is recognizable, in the sense of
[bottom-up finite tree automata](bottom-up-finite-tree-automata.md), if and only if the set of codes of the terms in $L$ is
definable in [WS$k$S](weak-monadic-second-order-logic-of-k-successors.md) (Thatcher and Wright; Doner). Both translations are
effective: a formula becomes an automaton by induction on the formula, using projection for existential quantifiers, and an
automaton becomes a formula that guesses a successful run with one set variable per state. More generally, a relation on
ground terms is in the class Rec of relations recognized by automata on tuples of terms if and only if it is definable in
WS$k$S.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)
- [Weak monadic second-order logic of $k$ successors](weak-monadic-second-order-logic-of-k-successors.md)

## Proof depends on

- [Determinization, closure and decision properties of regular tree languages](determinization-closure-and-decision-properties.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Lemma 3.3.4 (definable sets are recognizable), Lemma 3.3.6 (recognizable relations are definable) and Theorem 3.3.7, with the coding of terms in Section 3.3, and Section 1.9 on the introduction of tree automata by Doner and by Thatcher and Wright.
