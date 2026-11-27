# Single-sided games of repeating values with future obligations are undecidable

It is undecidable whether the system player has a winning strategy in a single-sided game whose winning condition is a formula of the logic of repeating values with non-nested future equality obligations, already with one Boolean variable of the environment and three data variables of the system.

**Theorem.** The winning strategy existence problem for single-sided $\mathrm{LRV}[\top, \approx, \rightarrow]$ [games of repeating values](logic-of-repeating-values-and-its-games.md) is undecidable, even when the formula giving the winning condition uses one Boolean variable belonging to environment and three data variables belonging to system.

This contrasts with the decidability of single-sided games with only past obligations, $\mathrm{LRV}[\top, \leftarrow]$, and even of their extension with past-time nested formulas. The source leaves open the case of fewer than three data variables of system.

## Depends on

- [The logic of repeating values and its games](logic-of-repeating-values-and-its-games.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the reachability problem for two-counter machines. System encodes a witnessing run with Boolean labels, each transition taking two consecutive positions, the second marked by a label *bis*. Data variables $x, y$ encode the two counters: a position labeled by an increment of the first counter carries a value in $x$ that may repeat in the future only once, at a position labeled by a matching decrement, so that the counter value is the number of earlier increments whose value is not yet matched. Variable $z$ of system and the Boolean variable $b$ of environment rule out illegal moves, a decrement of a zero counter or a zero test on a nonzero one: the formula is set up so that a cheating system must commit to repeating some data value in the future, and environment can then prevent that repetition from happening. System has a winning strategy if and only if the counter machine reaches its target.

## Sources

- D. Figueira, A. Majumdar and M. Praveen, "Playing with Repetitions in Data Words Using Energy Games", *Logical Methods in Computer Science* 16(3):1, 2020, doi:10.23638/LMCS-16(3:1)2020, <https://lmcs.episciences.org/4898>; numbering of arXiv:1802.07435v7: Theorem 6.1 with its proof in Section 6, and the decidability results of Sections 5 and 7.
