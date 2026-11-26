# Decidability of WS$k$S

For every $k \ge 1$, the weak monadic second-order theory of $k$ successors is decidable: there is an algorithm that decides
whether a given closed formula of [WS$k$S](weak-monadic-second-order-logic-of-k-successors.md) holds in the infinite $k$-ary
tree with second-order quantifiers ranging over finite sets (Thatcher and Wright). The formula is translated into a finite
tree automaton with the same solutions, and the truth of a closed formula reduces to the emptiness of that automaton.

## Depends on

- [Weak monadic second-order logic of $k$ successors](weak-monadic-second-order-logic-of-k-successors.md)

## Proof depends on

- [The WS$k$S-definable tree languages are the recognizable ones](wsks-definable-tree-languages-are-the-recognizable-ones.md)
- [Determinization, closure and decision properties of regular tree languages](determinization-closure-and-decision-properties.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Theorem 3.3.8 and its proof, and Section 3.6.2, which credits it to Thatcher and Wright (1968).
