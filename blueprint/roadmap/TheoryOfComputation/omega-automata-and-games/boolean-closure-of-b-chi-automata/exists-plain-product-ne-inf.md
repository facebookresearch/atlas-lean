# The plain product does not compute the intersection of Büchi languages

There are Büchi automata $A_1$ and $A_2$ such that the plain product, with accepting set
$F_1 \times F_2$, does not accept $L_\omega(A_1) \cap L_\omega(A_2)$. Vardi's example: both
two-state cyclic automata accept $a^\omega$, but visit their accepting states at alternate
instants, so their plain product is empty.

For automata on finite words the plain product does compute the intersection; on infinite
words the accepting visits of the two runs need not be simultaneous, and the correct
construction remembers which run must visit an accepting state next.

## Informally uses

- [Vardi's plain product is empty](language-plain-product-two-cycle.md).
- [A two-state cyclic automaton with an accepting state accepts every word](language-two-cycle.md).

## Background

- [Büchi automata are closed under intersection](exists-buchi-inf.md): the product with a
  pointer, which does compute the intersection.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, the example before Proposition 6.
