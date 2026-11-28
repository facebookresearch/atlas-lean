# Costed disjunction over a list

For a list $l$ and a map $f$ assigning to each element a Boolean result and a natural-number cost, the costed disjunction evaluates $f$ on every element, without short-circuiting, and returns the disjunction of the results together with the sum of the costs. The empty list gives result false at cost $0$.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
