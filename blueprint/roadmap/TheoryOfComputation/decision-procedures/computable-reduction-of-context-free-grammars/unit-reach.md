# Nonterminals reachable by unit productions in an encoded grammar

For an encoded
context-free grammar $g$ and a natural number $A$, let $n$ be the number of distinct nonterminals
mentioned in $g$ (the start, the left-hand sides, and the nonterminals on right-hand sides). The
list is obtained from the empty list by applying one round of unit reachability from $A$
exactly $n + 1$ times.

Its entries are exactly the nonterminals $B$ reachable from $A$ by a possibly empty chain of
unit productions $A \to \dots \to B$ of $g$; in particular $A$ itself is an entry.
